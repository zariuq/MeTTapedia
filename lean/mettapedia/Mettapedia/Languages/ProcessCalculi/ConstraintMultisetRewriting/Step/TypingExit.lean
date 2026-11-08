import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContractsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects

/-!
# The exit check against staged effects

The runtime typing draft checks a call's result after its body, so a check never precedes the body's
effects. Read as firings, the body is one firing and the exit check another, after it.

* **Sequential exit** (`sequential_exit_keeps_effects`): when the body is admitted and the exit check is
  refused at the configuration the body leaves, the body alone is a run, the body followed by the
  exit check is not, and every occurrence the body made is present at the end. A refused result
  leaves the body's effects in place.
* **Staged exit** (`staged_exit_no_residue`): put the exit check inside one staged block with the body
  (`StagedSourceEffects`). The block publishes once, at one cut. When the exit check is refused, the
  block leaves the caller's configuration unchanged; when both are admitted, it publishes the
  configuration the two firings leave (`staged_exit_commits`).

No change to the runtime is proposed; this is the structure of the two readings.

Control (`ExitControl`): a body that makes one occurrence and binds the result to `"s"`, against a
result declared `Number`. Sequentially, the occurrence stays (`sequential_leaves_occurrence`); staged,
the configuration is unchanged (`staged_leaves_nothing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingExit

open MeTTaCalculus.OccurrenceCommits (mem_fire)

section Generic

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- A firing as an instruction of a staged block. -/
def instruction (f : AnnotatedRuns.Firing T S O) : StagedSourceEffects.Instruction T S O :=
  ⟨f.rule, f.selection, f.queries⟩

/-- **Sequential exit.** The body is admitted, the exit check is refused after it: the body alone is
a run, the body then the exit check is not, and what the body made stays present. -/
theorem sequential_exit_keeps_effects (C₀ : Configuration T O) (body exit : AnnotatedRuns.Firing T S O)
    (admitted : body.Valid A label C₀) (refused : ¬ exit.Valid A label (body.result label C₀)) :
    (∃ r : (AnnotatedRuns.firstOrder A label).Run C₀,
        r.word.map Sigma.snd = [body] ∧ r.last = body.result label C₀) ∧
      (¬ ∃ r : (AnnotatedRuns.firstOrder A label).Run C₀, r.word.map Sigma.snd = [body, exit]) ∧
      ∀ o ∈ body.selection.made, o ∈ (body.result label C₀).present := by
  refine ⟨⟨.cons body admitted (.nil _), rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨r, word⟩
    cases r with
    | nil => simp [Interface.Step.Run.word] at word
    | cons f fAdmitted rest =>
        cases rest with
        | nil => simp [Interface.Step.Run.word] at word
        | cons g gAdmitted _ =>
            simp only [Interface.Step.Run.word, List.map_cons, List.cons.injEq] at word
            obtain ⟨rfl, rfl, -⟩ := word
            exact refused gAdmitted
  · intro o made
    show o ∈ MeTTaCalculus.OccurrenceCommits.fire C₀.present (body.selection.commit (T := T))
    rw [mem_fire]
    exact .inr (by simpa [Selection.commit] using made)

/-- The body and its exit check run in a staged block exactly when they run in sequence. -/
theorem staged_executable_iff (C₀ : Configuration T O) (body exit : AnnotatedRuns.Firing T S O) :
    StagedSourceEffects.Executable A label C₀ [instruction body, instruction exit] ↔
      AnnotatedRuns.Executable A label C₀ [body, exit] :=
  Iff.rfl

/-- **Staged exit.** When the exit check is refused after the body, the staged block leaves the
caller's configuration unchanged: one commit at one cut, and no residue. -/
theorem staged_exit_no_residue (C₀ after : Configuration T O) (body exit : AnnotatedRuns.Firing T S O)
    (refused : ¬ exit.Valid A label (body.result label C₀))
    (result : StagedSourceEffects.CompiledResult A label
      (StagedSourceEffects.compile label [instruction body, instruction exit]) C₀ after) :
    after = C₀ :=
  StagedSourceEffects.refused_has_no_residue
    (fun ready : StagedSourceEffects.Executable A label C₀ [instruction body, instruction exit] =>
      refused ready.2.1) result

/-- When the body and the exit check are both admitted, the staged block publishes the configuration
the two firings leave. -/
theorem staged_exit_commits (C₀ after : Configuration T O) (body exit : AnnotatedRuns.Firing T S O)
    (ready : AnnotatedRuns.Executable A label C₀ [body, exit])
    (result : StagedSourceEffects.CompiledResult A label
      (StagedSourceEffects.compile label [instruction body, instruction exit]) C₀ after) :
    after = AnnotatedRuns.follow label C₀ [body, exit] := by
  rcases (StagedSourceEffects.compiled_result_iff_source A label _ C₀ after).mp result with
    ⟨_, same⟩ | ⟨refused, _⟩
  · rw [same, AnnotatedRuns.follow_eq_plain]
    rfl
  · exact absurd ready refused

end Generic

namespace ExitControl

open Mettapedia.Logic.ConstraintTypes
open TypingFirings TypingContractsControls

/-- The body: it makes occurrence `7` and binds the result `R` (program variable `1`) to `"s"`. -/
def body : AnnotatedRuns.Firing TypingContractsControls.T (Instantiation Nat Nat Name Empty Sym typeArity valueArity isAtom) Nat :=
  ⟨⟨[], [], [(.value (.var 1), .value (ofTree (leaf (.text "s"))))], [], [label 7]⟩, [], ⟨[], [], [7]⟩⟩

/-- The exit check: `R` must be a `Number`. -/
def exit : AnnotatedRuns.Firing TypingContractsControls.T (Instantiation Nat Nat Name Empty Sym typeArity valueArity isAtom) Nat :=
  tellFiring [require () (.var 1) (.closed .number)]

theorem body_admitted : body.Valid (action decls isAtom) label start := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [body, Selection.commit]
  · simp [body, Selection.commit]
  · simp [body, Selection.commit]
  · simp [body, Selection.commit, start]
  · simp [body, Selection.commit]
  · show (action decls isAtom).Consistent ([] ++ [] ++ [] ++ _)
    rw [consistent_iff seed]
    refine ⟨pointAt isAtom (leaf (.text "s")) .number (by simp [isAtom]), ?_⟩
    simp [Holds, Term.meaning, OpenTree.evaluate, pointAt, body]
  · intro check member
    cases member
  · intro query member
    cases member

theorem body_result_equations :
    (body.result label start).equations =
      [(.value (.var 1), .value (ofTree (leaf (.text "s"))))] := rfl

theorem exit_refused : ¬ exit.Valid (action decls isAtom) label (body.result label start) := by
  intro valid
  have admitted : (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits
      (s := body.result label start) exit := valid
  rw [exit, tell_admits_iff, consistent_iff seed, body_result_equations] at admitted
  obtain ⟨ρ, holds⟩ := admitted
  obtain ⟨bound, required⟩ := holds_append.mp holds
  have value := (holds_bind_iff' ρ).mp bound
  have typed := (holds_require ρ () (.var 1) (.closed .number)).mp required
  change DeclarationTyping.HasType decls () (ρ.values 1) (.closed .number) at typed
  rw [value] at typed
  rcases types_of_node (.text "s") Fin.elim0 _ typed with wrong | wrong <;> cases wrong
where
  holds_bind_iff' (ρ : Pt isAtom) :
      Holds decls isAtom ρ [(.value (.var 1), .value (ofTree (leaf (.text "s"))))] ↔
        ρ.values 1 = leaf (.text "s") := by
    simp [Holds, Term.meaning, OpenTree.evaluate]

/-- **Sequentially, the refused result leaves the body's occurrence.** -/
theorem sequential_leaves_occurrence :
    (¬ ∃ r : (AnnotatedRuns.firstOrder (action decls isAtom) label).Run start,
        r.word.map Sigma.snd = [body, exit]) ∧
      7 ∈ (body.result label start).present :=
  have law := sequential_exit_keeps_effects (action decls isAtom) label start body exit body_admitted
    exit_refused
  ⟨law.2.1, law.2.2 7 (List.mem_singleton.mpr rfl)⟩

/-- **Staged, the refused result leaves nothing.** -/
theorem staged_leaves_nothing (after : Configuration TypingContractsControls.T Nat)
    (result : StagedSourceEffects.CompiledResult (action decls isAtom) label
      (StagedSourceEffects.compile label [instruction body, instruction exit]) start after) :
    after = start ∧ 7 ∉ after.present := by
  have same := staged_exit_no_residue (action decls isAtom) label start after body exit exit_refused result
  subst same
  exact ⟨rfl, by simp [start]⟩

end ExitControl

#print axioms sequential_exit_keeps_effects
#print axioms staged_executable_iff
#print axioms staged_exit_no_residue
#print axioms staged_exit_commits
#print axioms ExitControl.body_admitted
#print axioms ExitControl.exit_refused
#print axioms ExitControl.sequential_leaves_occurrence
#print axioms ExitControl.staged_leaves_nothing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingExit
