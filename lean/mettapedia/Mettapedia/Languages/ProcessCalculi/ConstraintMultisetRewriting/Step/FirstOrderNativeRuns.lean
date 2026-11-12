import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCoexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsTensor

/-!
# Raw native runs and the existing first-order executable schedules

The translation retains every firing and the actual endpoint. Consistency is
the only additional condition at an empty schedule. A nonempty native run
already supplies that condition through admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder Executable follow)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

abbrev sites {state : Configuration T O} (run : (firstOrder A label).toStep.Run state) :
    List (Firing T S O) := run.word.map Sigma.snd

def ofExecutable : ∀ (state : Configuration T O) (word : List (Firing T S O)),
    Executable A label state word → (firstOrder A label).toStep.Run state
  | state, [], _ => .nil state
  | _, f :: rest, ready => .cons f ready.1 (ofExecutable _ rest ready.2)

theorem sites_ofExecutable : ∀ (state : Configuration T O) (word : List (Firing T S O))
    (ready : Executable A label state word), sites A label (ofExecutable A label state word ready) = word
  | _, [], _ => rfl
  | state, f :: rest, ready => by
      change f :: sites A label (ofExecutable A label (f.result label state) rest ready.2) = f :: rest
      rw [sites_ofExecutable _ rest ready.2]

theorem last_eq_follow : ∀ {state : Configuration T O} (run : (firstOrder A label).toStep.Run state),
    run.last = follow label state (sites A label run)
  | _, .nil _ => rfl
  | _, .cons _ _ rest => last_eq_follow rest

theorem sites_injective {state : Configuration T O} :
    Function.Injective (sites A label (state := state)) := by
  intro first
  induction first with
  | nil state =>
      intro second same
      cases second with
      | nil => rfl
      | cons => exact False.elim (List.cons_ne_nil _ _ same.symm)
  | cons f allowed rest ih =>
      intro second same
      cases second with
      | nil => exact False.elim (List.cons_ne_nil _ _ same)
      | cons g permitted later =>
          obtain ⟨rfl, tails⟩ := List.cons.inj same
          have equal := ih tails
          cases equal
          rfl

theorem executable_of_run : ∀ {state : Configuration T O} (run : (firstOrder A label).toStep.Run state),
    A.Consistent state.equations → Executable A label state (sites A label run)
  | _, .nil _, consistent => consistent
  | _, .cons _ allowed rest, _ => ⟨allowed, executable_of_run rest allowed.firing.consistent⟩

theorem executable_of_nonempty : ∀ {state : Configuration T O} (run : (firstOrder A label).toStep.Run state),
    sites A label run ≠ [] → Executable A label state (sites A label run)
  | _, .nil _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ allowed rest, _ => ⟨allowed, executable_of_run A label rest allowed.firing.consistent⟩

theorem exists_run_iff (state : Configuration T O) (word : List (Firing T S O)) :
    (∃ run : (firstOrder A label).toStep.Run state, sites A label run = word) ↔
      word = [] ∨ Executable A label state word := by
  constructor
  · rintro ⟨run, rfl⟩
    by_cases empty : sites A label run = []
    · exact Or.inl empty
    · exact Or.inr (executable_of_nonempty A label run empty)
  · rintro (rfl | ready)
    · exact ⟨.nil state, rfl⟩
    · exact ⟨ofExecutable A label state word ready, sites_ofExecutable A label state word ready⟩

theorem consistent_run_iff (state : Configuration T O) (word : List (Firing T S O)) :
    (∃ run : (firstOrder A label).toStep.Run state,
      sites A label run = word ∧ A.Consistent state.equations) ↔ Executable A label state word := by
  constructor
  · rintro ⟨run, rfl, consistent⟩
    exact executable_of_run A label run consistent
  · intro ready
    refine ⟨ofExecutable A label state word ready, sites_ofExecutable A label state word ready, ?_⟩
    cases word with
    | nil => exact ready
    | cons _ _ =>
        obtain ⟨σ, solved⟩ := ready.1.firing.consistent
        exact ⟨σ, ready.1.firing.refines σ solved⟩

def executableEquivRun (state : Configuration T O) (consistent : A.Consistent state.equations) :
    {word : List (Firing T S O) // Executable A label state word} ≃ (firstOrder A label).toStep.Run state where
  toFun source := ofExecutable A label state source.1 source.2
  invFun run := ⟨sites A label run, executable_of_run A label run consistent⟩
  left_inv source := Subtype.ext (sites_ofExecutable A label state source.1 source.2)
  right_inv run := sites_injective A label
    (sites_ofExecutable A label state (sites A label run) (executable_of_run A label run consistent))

theorem sites_append {state : Configuration T O} (run : (firstOrder A label).toStep.Run state)
    (later : (firstOrder A label).toStep.Run run.last) :
    sites A label (run.append later) = sites A label run ++ sites A label later := by
  rw [sites, Step.Run.word_append, List.map_append]

abbrev nativePair (left right : Configuration T O) :
    (firstOrder A label).toStep.effectCore.NativePair left right where
  state := AnnotatedRuns.tensor left right
  leftMap := A.identity
  rightMap := A.identity
  knowledge := by
    intro later σ
    change (Frames.ofSubstitution A).Models σ (left.equations ++ right.equations) ↔
      (Frames.ofSubstitution A).Models σ
        ((Frames.ofSubstitution A).applyStore ((Frames.ofSubstitution A).id PUnit.unit) left.equations ++
          (Frames.ofSubstitution A).applyStore ((Frames.ofSubstitution A).id PUnit.unit) right.equations)
    rw [Frames.applyStore_id, Frames.applyStore_id]
  present := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
