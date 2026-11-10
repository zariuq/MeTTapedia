import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSubmission

/-! # An executable constraint-store consumer of the authored event presentation

States contain arbitrary finite lists of Boolean equations. Substitutions are
all Boolean functions, so the equation `true = false` is a genuine constraint:
identity fails it and either constant substitution solves it. The prepared
effect tells that equation, while this admission profile refuses a duplicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls

open Interface
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

def frame : Frames (fun _ : Unit => Bool) (fun _ _ : Unit => Bool → Bool) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act f t := f t
  id _ := id
  comp g f := g ∘ f
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b f s t same; exact congrArg f same

abbrev Store := EquationStore Bool
abbrev effect := EffectCore.tell frame () [(true, false)]

def permission : effect.Admission := fun {s} _ _ => (true, false) ∉ s

theorem prepares (s : Store) (f : Unit) : effect.Prepares (s := s) f :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), (fun _ => false), by intro e _; rfl⟩⟩

def decisions : Decisions effect permission where
  prepare {s} f := .isTrue (prepares s f)
  permit {s} _ _ := inferInstanceAs (Decidable ((true, false) ∉ s))

def boolPattern : Bool → Pattern
  | false => .apply "False" []
  | true => .apply "True" []

def readBool : Pattern → Option Bool
  | .apply "False" [] => some false
  | .apply "True" [] => some true
  | _ => none

@[simp] theorem readBool_pattern (b : Bool) : readBool (boolPattern b) = some b := by
  cases b <;> rfl

def equationPattern (e : Bool × Bool) : Pattern :=
  .apply "Equation" [boolPattern e.1, boolPattern e.2]

def readEquation : Pattern → Option (Bool × Bool)
  | .apply "Equation" [a, b] => do pure (← readBool a, ← readBool b)
  | _ => none

@[simp] theorem readEquation_pattern (e : Bool × Bool) :
    readEquation (equationPattern e) = some e := by
  rcases e with ⟨a, b⟩
  simp [readEquation, equationPattern]

def storePattern (s : Store) : Pattern := .apply "Store" (s.map equationPattern)

def readStore : Pattern → Option Store
  | .apply "Store" entries => entries.mapM readEquation
  | _ => none

theorem readStore_pattern (s : Store) : readStore (storePattern s) = some s := by
  change (s.map equationPattern).mapM readEquation = some s
  induction s with
  | nil => rfl
  | cons e s ih => simp [List.mapM_cons, ih]

def statePresentation : PatternPresentation Store where
  key := ⟨"tcalc.boolean-equations", 1⟩
  expand := readStore
  view := storePattern
  expand_view := readStore_pattern

def firingPresentation : PatternPresentation ((_ : Store) × Unit) where
  key := ⟨"tcalc.tell-boolean-equation", 1⟩
  expand p := match p with
    | .apply "Tell" [s] => (readStore s).map fun store => ⟨store, ()⟩
    | _ => none
  view c := .apply "Tell" [storePattern c.1]
  expand_view c := by
    rcases c with ⟨s, f⟩
    cases f
    simp [readStore_pattern]

def encoding : Encoding Store (fun _ => Unit) := ⟨statePresentation, firingPresentation⟩

def queries : Queries := effectQueries effect permission encoding decisions

def source (s : Store) : Pattern :=
  request (storePattern s) (.apply "Tell" [storePattern s])

/-- The authored rule executes the real store update for every finite store. -/
theorem execution_all_stores (s : Store) :
    rewriteStepWithPremisesUsing queries.relations language (source s) =
      if (true, false) ∈ s then [] else [atState (storePattern (s ++ [(true, false)]))] := by
  change rewriteStepWithPremisesUsing
    (effectQueries effect permission encoding decisions).relations language
    (request (encoding.state.view (sort := ()) s)
      (encoding.firing.view (sort := ()) ⟨s, ()⟩)) = _
  rw [execution, preparation_encoded, permission_encoded]
  simp only [dif_pos (prepares s ())]
  by_cases told : (true, false) ∈ s <;>
    simp [permission, told, encoding, statePresentation]

theorem tells_constraint :
    rewriteStepWithPremisesUsing queries.relations language (source []) =
      [atState (storePattern [(true, false)])] := by
  simpa using execution_all_stores []

theorem refuses_duplicate :
    rewriteStepWithPremisesUsing queries.relations language (source [(true, false)]) = [] := by
  simpa using execution_all_stores [(true, false)]

theorem duplicate_is_still_prepared :
    (queries.prepare (storePattern [(true, false)])
      (.apply "Tell" [storePattern [(true, false)]])).isSome := by
  decide +kernel

theorem false_target_refused :
    atState (storePattern [(false, true)]) ∉
      rewriteStepWithPremisesUsing queries.relations language (source []) := by
  rw [tells_constraint]
  decide +kernel

theorem wrong_source_index_refused :
    rewriteStepWithPremisesUsing queries.relations language
      (request (storePattern [(true, false)]) (.apply "Tell" [storePattern []])) = [] := by
  decide +kernel

theorem object_variable_is_not_a_query_hole :
    rewriteStepWithPremisesUsing queries.relations language
      (request (.fvar "s") (.apply "Tell" [storePattern []])) = [] := by
  decide +kernel

theorem stale_version_refused (s : Store) :
    Mettapedia.GSLT.Parsing.ExactPresentation.expandDocument statePresentation
      (sort := ()) ⟨⟨"tcalc.boolean-equations", 0⟩, storePattern s⟩ = none := by
  rfl

/-- An incorrect lowering can keep every valid transition while adding others. -/
def bypassPermission : Queries := { queries with permit := fun _ _ => true }

theorem forward_simulation_is_insufficient (s f target : Pattern)
    (executed : target ∈ rewriteStepWithPremisesUsing queries.relations language (request s f)) :
    target ∈ rewriteStepWithPremisesUsing bypassPermission.relations language (request s f) := by
  rw [execution] at executed ⊢
  change target ∈ (match queries.prepare s f with
    | none => []
    | some t => if true then [atState t] else [])
  split at executed
  · contradiction
  · rename_i result prepared
    rw [prepared]
    simpa using (by split at executed <;> simp_all : target ∈ [atState result])

theorem bypass_invents_a_transition :
    atState (storePattern [(true, false), (true, false)]) ∈
      rewriteStepWithPremisesUsing bypassPermission.relations language
        (source [(true, false)]) := by
  decide +kernel

theorem invented_transition_has_no_event :
    ¬Nonempty (effect.Event permission [(true, false)] [(true, false), (true, false)]) := by
  rintro ⟨event⟩
  exact event.permitted (List.mem_singleton_self _)

/-- Knowledge preservation cannot authorize bypassing the language's permission. -/
theorem refused_effect_still_refines (σ : Bool → Bool)
    (solved : frame.Models (a := ()) (b := ()) σ [(true, false), (true, false)]) :
    frame.Models (a := ()) (b := ()) σ [(true, false)] := by
  exact effect.models_along (s := [(true, false)]) ()
    (prepares [(true, false)] ()) σ solved

/-- Bypassing duplicate refusal breaks the store's no-duplicates invariant,
although the same effect still refines knowledge. -/
theorem bypass_breaks_language_invariant :
    ([(true, false)] : Store).Nodup ∧
      ¬ ([(true, false), (true, false)] : Store).Nodup ∧
      (∀ σ : Bool → Bool,
        frame.Models (a := ()) (b := ()) σ [(true, false), (true, false)] →
          frame.Models (a := ()) (b := ()) σ [(true, false)]) :=
  ⟨by decide +kernel, by decide +kernel, refused_effect_still_refines⟩

theorem told_constraint_is_genuine :
    ¬frame.Models (a := ()) (b := ()) id [(true, false)] := by
  intro solved
  have impossible := solved (true, false) (List.mem_singleton_self _)
  cases impossible

def tellEvent : ExecutedEvent queries (storePattern []) (storePattern [(true, false)]) where
  firing := .apply "Tell" [storePattern []]
  executed := by
    change atState (storePattern [(true, false)]) ∈
      rewriteStepWithPremisesUsing queries.relations language (source [])
    rw [tells_constraint]
    exact List.mem_singleton_self _

def tellPath : @Quiver.Path (ExecutionObject queries) _
    (storePattern []) (storePattern [(true, false)]) := .cons .nil tellEvent

theorem real_lowering_has_administrative_step :
    (Submission.lower queries tellPath).length = 2 ∧ tellPath.length = 1 := by
  constructor <;> rfl

theorem real_lowering_reflects :
    Submission.reflect queries (Submission.lower queries tellPath) = tellPath :=
  Submission.reflect_lower queries tellPath

/-- A refused request can be submitted, but cannot become a successful event. -/
def refusedSubmission : @Quiver.Path (Submission.Machine queries) _
    (.ready (storePattern [(true, false)]))
    (.waiting (storePattern [(true, false)]) (.apply "Tell" [storePattern [(true, false)]])) :=
  .cons .nil (.select _ _)

theorem submission_is_not_execution (target : Pattern) :
    ¬Nonempty (Submission.Transition queries
      (.waiting (storePattern [(true, false)]) (.apply "Tell" [storePattern [(true, false)]]))
      (.ready target)) := by
  rintro ⟨step⟩
  cases step with
  | execute admitted =>
      change atState target ∈ rewriteStepWithPremisesUsing queries.relations language
        (source [(true, false)]) at admitted
      rw [refuses_duplicate] at admitted
      exact List.not_mem_nil admitted

theorem refused_submission_records_no_firing :
    (Submission.reflect queries refusedSubmission).length = 0 := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls
