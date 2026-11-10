import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mettapedia.GSLT.Parsing.ExactPresentation

/-!
# Interpretation of the authored event queries

An encoding uses the existing exact, versioned presentation interface. A
candidate includes its source index. Preparation and permission are decided
separately, and query rows are built from those decisions and the actual
prepared result. No row is granted authority merely by its relation name.

Executable decisions are an explicit capability of a profile. The effect
calculus itself does not require them, finite carriers, or an evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Interface

universe uO uT uH uOcc uS uF

abbrev PatternPresentation (α : Type uS) :=
  Mettapedia.GSLT.Parsing.ExactPresentation.Presentation
    (fun _ : Unit => α) (fun _ : Unit => Pattern)

structure Encoding (State : Type uS) (Firing : State → Type uF) where
  state : PatternPresentation State
  firing : PatternPresentation ((s : State) × Firing s)

theorem PatternPresentation.view_injective {α : Type uS} (p : PatternPresentation α) :
    Function.Injective (p.view (sort := ())) := by
  intro a b same
  have decoded := congrArg (p.expand (sort := ())) same
  simpa only [p.expand_view, Option.some.injEq] using decoded

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

/-- A decision is evidence for the semantic proposition, not a host-issued tag. -/
structure Decisions (E : EffectCore X O State Firing) (allow : E.Admission) where
  prepare : ∀ {s : State} (f : Firing s), Decidable (E.Prepares f)
  permit : ∀ {s : State} (f : Firing s) (p : E.Prepares f), Decidable (allow f p)

/-- A semantic interpretation exists even for an undecidable profile. This
noncomputable construction is not an executable solver or an evaluation policy. -/
noncomputable def Decisions.ofClassical (E : EffectCore X O State Firing)
    (allow : E.Admission) : Decisions E allow where
  prepare f := Classical.propDecidable (E.Prepares f)
  permit f p := Classical.propDecidable (allow f p)

variable (E : EffectCore X O State Firing) (allow : E.Admission)
  (code : Encoding State Firing) (decision : Decisions E allow)

def effectQueries : Queries where
  prepare source firing :=
    match code.firing.expand (sort := ()) firing with
    | none => none
    | some c =>
        if code.state.view (sort := ()) c.1 = source ∧ code.firing.view (sort := ()) c = firing then
          @dite _ (E.Prepares c.2) (decision.prepare c.2)
            (fun p => some (code.state.view (sort := ()) (E.preparedResult c.2 p))) (fun _ => none)
        else none
  permit source firing :=
    match code.firing.expand (sort := ()) firing with
    | none => false
    | some c =>
        if code.state.view (sort := ()) c.1 = source ∧ code.firing.view (sort := ()) c = firing then
          @dite _ (E.Prepares c.2) (decision.prepare c.2)
            (fun p => @decide (allow c.2 p) (decision.permit c.2 p)) (fun _ => false)
        else false

theorem preparation_encoded {s : State} (f : Firing s) :
    (effectQueries E allow code decision).prepare (code.state.view (sort := ()) s)
      (code.firing.view (sort := ()) ⟨s, f⟩) =
        @dite _ (E.Prepares f) (decision.prepare f)
          (fun p => some (code.state.view (sort := ()) (E.preparedResult f p))) (fun _ => none) := by
  simp [effectQueries, code.firing.expand_view]

theorem permission_encoded {s : State} (f : Firing s) :
    (effectQueries E allow code decision).permit (code.state.view (sort := ()) s)
      (code.firing.view (sort := ()) ⟨s, f⟩) =
        @dite _ (E.Prepares f) (decision.prepare f)
          (fun p => @decide (allow f p) (decision.permit f p)) (fun _ => false) := by
  simp [effectQueries, code.firing.expand_view]

/-- Every returned preparation comes from an actual indexed candidate and result. -/
theorem preparation_reflects {source firing target : Pattern}
    (found : (effectQueries E allow code decision).prepare source firing = some target) :
    ∃ (c : (s : State) × Firing s) (p : E.Prepares c.2),
      code.state.view (sort := ()) c.1 = source ∧
      code.firing.view (sort := ()) c = firing ∧
      code.state.view (sort := ()) (E.preparedResult c.2 p) = target := by
  change (match code.firing.expand (sort := ()) firing with
    | none => none
    | some c => if code.state.view (sort := ()) c.1 = source ∧
        code.firing.view (sort := ()) c = firing then
        @dite _ (E.Prepares c.2) (decision.prepare c.2)
          (fun p => some (code.state.view (sort := ()) (E.preparedResult c.2 p)))
          (fun _ => none)
      else none) = some target at found
  split at found
  · contradiction
  · rename_i c decoded
    split at found
    · rename_i encoded
      split at found
      · rename_i prepared
        exact ⟨c, prepared, encoded.1, encoded.2, Option.some.inj found⟩
      · contradiction
    · contradiction

/-- No malformed candidate, invented source, or extra target can execute. -/
theorem execution_reflects {source firing target : Pattern}
    (executed : target ∈ rewriteStepWithPremisesUsing
      (effectQueries E allow code decision).relations language (request source firing)) :
    ∃ (c : (s : State) × Firing s) (p : E.Prepares c.2),
      code.state.view (sort := ()) c.1 = source ∧
      code.firing.view (sort := ()) c = firing ∧ allow c.2 p ∧
      target = atState (code.state.view (sort := ()) (E.preparedResult c.2 p)) := by
  rw [execution] at executed
  split at executed
  · contradiction
  · rename_i output prepared
    obtain ⟨c, p, source_eq, firing_eq, result_eq⟩ :=
      preparation_reflects E allow code decision prepared
    subst source
    subst firing
    rw [permission_encoded] at executed
    simp only [dif_pos p] at executed
    let _ := decision.permit c.2 p
    split at executed
    · rename_i admitted
      refine ⟨c, p, rfl, rfl, of_decide_eq_true admitted, ?_⟩
      simpa only [result_eq, List.mem_singleton] using executed
    · contradiction

/-- Preservation and reflection of the actual authored rule for one candidate. -/
theorem execution_iff_prepared {s t : State} (f : Firing s) :
    atState (code.state.view (sort := ()) t) ∈ rewriteStepWithPremisesUsing
      (effectQueries E allow code decision).relations language
      (request (code.state.view (sort := ()) s) (code.firing.view (sort := ()) ⟨s, f⟩)) ↔
      ∃ p : E.Prepares f, allow f p ∧ E.preparedResult f p = t := by
  rw [execution, preparation_encoded, permission_encoded]
  by_cases prepared : E.Prepares f
  · simp only [dif_pos prepared]
    let _ := decision.permit f prepared
    by_cases admitted : allow f prepared
    ·
        simp only [decide_eq_true admitted, if_true, List.mem_singleton]
        constructor
        · intro same
          have states := Pattern.apply.inj same
          have target := List.cons.inj states.2
          exact ⟨prepared, admitted, (code.state.view_injective target.1).symm⟩
        · rintro ⟨_, _, rfl⟩
          rfl
    ·
        simp only [decide_eq_false admitted, Bool.false_eq_true, if_false, List.not_mem_nil,
          false_iff]
        rintro ⟨p, admitted, _⟩
        exact ‹¬ allow f prepared› admitted
  · simp only [dif_neg prepared, List.not_mem_nil, false_iff]
    rintro ⟨p, _, _⟩
    exact prepared p

/-- The event retains the selected firing, even when other firings share endpoints. -/
theorem execution_iff_event {s t : State} (f : Firing s) :
    atState (code.state.view (sort := ()) t) ∈ rewriteStepWithPremisesUsing
      (effectQueries E allow code decision).relations language
      (request (code.state.view (sort := ()) s) (code.firing.view (sort := ()) ⟨s, f⟩)) ↔
      ∃ event : E.Event allow s t, event.firing = f := by
  rw [execution_iff_prepared]
  constructor
  · rintro ⟨p, admitted, target⟩
    exact ⟨⟨f, p, admitted, target⟩, rfl⟩
  · rintro ⟨⟨g, p, admitted, target⟩, rfl⟩
    exact ⟨p, admitted, target⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
