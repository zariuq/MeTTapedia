import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SequentialComposition
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Finite conditional composition of occurrence schedules

A compiled schedule contains a finite initial precondition and a net commit.
Compilation transports later checks backwards, retaining freshness even when
an intermediate creation is consumed and disappears from the net update.
The result contains no callback that executes the original schedule.

The theorem concerns executability and the final occurrence store. It does not
identify event traces or enumerate overlaps of open rule schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v
variable {O : Type u} [DecidableEq O] {R : Type v}

structure CompiledSchedule (O : Type u) (R : Type v) where
  condition : CommitPrecondition O R
  effect : Commit O R

namespace CompiledSchedule

def empty : CompiledSchedule O R :=
  ⟨⟨∅, ∅, [], true⟩, ⟨∅, ∅, ∅, []⟩⟩

def prepend (label : O → R) (first : Commit O R) (tail : CompiledSchedule O R) :
    CompiledSchedule O R :=
  ⟨(CommitPrecondition.ofCommit first).and (tail.condition.before label first),
    first.compose tail.effect⟩

def compile (label : O → R) : List (Commit O R) → CompiledSchedule O R
  | [] => empty
  | first :: rest => prepend label first (compile label rest)

theorem compile_correct (label : O → R) (schedule : List (Commit O R)) (store : Finset O) :
    ((compile label schedule).condition.Holds label store ↔ Executable label store schedule) ∧
      ((compile label schedule).condition.Holds label store →
        Enabled label store (compile label schedule).effect ∧
          fire store (compile label schedule).effect = fireList store schedule) := by
  induction schedule generalizing store with
  | nil =>
    have guard : (compile label []).condition.Holds label store := by
      simp [compile, empty, CommitPrecondition.Holds]
    refine ⟨⟨fun _ => .nil _, fun _ => guard⟩, fun _ => ⟨?_, ?_⟩⟩
    · constructor <;> simp [compile, empty]
    · simp [compile, empty, fire]
  | cons first rest ih =>
    have guardIff : (compile label (first :: rest)).condition.Holds label store ↔
        Enabled label store first ∧ (compile label rest).condition.Holds label (fire store first) := by
      change ((CommitPrecondition.ofCommit first).and
        ((compile label rest).condition.before label first)).Holds label store ↔ _
      rw [CommitPrecondition.and_holds_iff, CommitPrecondition.ofCommit_holds_iff]
      exact and_congr_right fun enabled => CommitPrecondition.before_holds_iff _ enabled
    refine ⟨?_, ?_⟩
    · rw [guardIff, executable_cons_iff, (ih (fire store first)).1]
    · intro admitted
      obtain ⟨enabled, later⟩ := guardIff.mp admitted
      obtain ⟨tailEnabled, tailEffect⟩ := (ih (fire store first)).2 later
      exact ⟨Commit.compose_enabled enabled tailEnabled,
        (Commit.compose_fire enabled tailEnabled).trans tailEffect⟩

theorem compile_condition_iff (label : O → R) (schedule : List (Commit O R)) (store : Finset O) :
    (compile label schedule).condition.Holds label store ↔ Executable label store schedule :=
  (compile_correct label schedule store).1

theorem compile_effect {label : O → R} {schedule : List (Commit O R)} {store : Finset O}
    (executable : Executable label store schedule) :
    fire store (compile label schedule).effect = fireList store schedule :=
  ((compile_correct label schedule store).2
    ((compile_condition_iff label schedule store).mpr executable)).2

/-- Both admission and the final occurrence store are preserved and reflected. -/
theorem compile_exact (label : O → R) (schedule : List (Commit O R)) (store result : Finset O) :
    ((compile label schedule).condition.Holds label store ∧
      result = fire store (compile label schedule).effect) ↔
    (Executable label store schedule ∧ result = fireList store schedule) := by
  constructor
  · rintro ⟨guard, resultEq⟩
    have executable := (compile_condition_iff label schedule store).mp guard
    exact ⟨executable, resultEq.trans (compile_effect executable)⟩
  · rintro ⟨executable, resultEq⟩
    exact ⟨(compile_condition_iff label schedule store).mpr executable,
      resultEq.trans (compile_effect executable).symm⟩

/-- Parenthesizing sequential blocks preserves admission and the final store. -/
theorem compile_append {label : O → R} {first second : List (Commit O R)} {store : Finset O}
    (executable : Executable label store (first ++ second)) :
    fire store (compile label (first ++ second)).effect =
      fire (fire store (compile label first).effect) (compile label second).effect := by
  obtain ⟨one, two⟩ := executable_append_iff.mp executable
  rw [compile_effect executable, fireList_append, compile_effect one, compile_effect two]

/-- Any invariant of the admitted occurrence steps holds after their computed net update. -/
theorem preserves {label : O → R} {schedule : List (Commit O R)} {store : Finset O}
    {invariant : Finset O → Prop}
    (preserve : ∀ commit ∈ schedule, ∀ state, Enabled label state commit →
      invariant state → invariant (fire state commit))
    (admitted : (compile label schedule).condition.Holds label store) (initial : invariant store) :
    invariant (fire store (compile label schedule).effect) := by
  have executable := (compile_condition_iff label schedule store).mp admitted
  rw [compile_effect executable]
  clear admitted
  induction executable with
  | nil => exact initial
  | @cons before first rest enabled tail ih =>
    apply ih
    · intro commit member
      exact preserve commit (by simp [member])
    · exact preserve first (by simp) before enabled initial

namespace Controls

def create : Commit Nat Unit := ⟨∅, ∅, {0}, []⟩
def consume : Commit Nat Unit := ⟨{0}, ∅, ∅, []⟩
def inspect : Commit Nat Unit := ⟨∅, {0}, ∅, []⟩
def label (_ : Nat) : Unit := ()

theorem create_consume_admitted : (compile label [create, consume]).condition.Holds label ∅ := by decide
theorem create_consume_effect_empty : fire ∅ (compile label [create, consume]).effect = ∅ := by decide

/-- The empty net effect must not erase the intermediate allocation's freshness condition. -/
theorem reused_creation_refused : ¬(compile label [create, consume]).condition.Holds label {0} := by decide

theorem repeated_reads_share_occurrence : (compile label [inspect, inspect]).condition.Holds label {0} := by decide
theorem double_consumption_refused : ¬(compile label [consume, consume]).condition.Holds label {0} := by decide

end Controls
end CompiledSchedule
end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
