import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersLeftmost

/-!
# Leftmost-innermost reduction on the step

R100's innermost firings (`ProgramBindersStrategy`) are guarded firings of the contextual step,
keyed by a position, an equation and a depth bound; their checks refute every match strictly inside
the redex. A leftmost-innermost firing is such a firing at a **clear** key: at each application
where the key's position goes into the argument, the function is normal (`LeftClear`). The function
is a sibling of the key's own context, a source term fixed by the key, so clearness is a condition
on the key and adds no check to the firing.

With no `atom` declarations (the step's checks look at every position strictly inside the redex):

- `leftmost_step_iff`: at a call every solution reads the same way, one firing at a clear key is
  exactly one leftmost-innermost reduction (`LeftmostInnermost`), both ways.
- `leftmost_reflected`, `leftmost_runs_backward`: every reading after a run of such firings is
  reached by leftmost-innermost reduction.
- `leftmost_execution_iff`: for determinate equations, leftmost-innermost reduction reaches exactly
  the readings of runs of leftmost-innermost firings.

With declarations, a firing at a clear, evaluated key is sound (`leftmost_step_sound_atoms`); it is
complete for reductions whose redex has no match strictly inside, frozen positions included
(`leftmost_step_complete_atoms`). The step's checks cannot leave frozen positions out: whether a
position inside the redex is frozen depends on heads the call's solutions may still choose.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.LeftmostStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open Nested (raiseAt raisedSchema grammar)
open Strategy
open Leftmost

variable {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term)

/-- A position clear of redexes to its left, with no declarations. -/
abbrev Clear {Δ : Ctx sig} (context : Context Γ Δ) : Prop :=
  LeftClear (noDeclarations (Var Γ .term)) program some context

theorem innermostAt_none_iff {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) :
    InnermostAt (noDeclarations (Var Γ .term)) program some context inner ↔
      MatchesAt program context inner ∧ InnerNormal program context inner :=
  ⟨fun ⟨_, matched, normal⟩ => ⟨matched, (innerNormalA_iff program context inner).mp normal⟩,
    fun ⟨matched, normal⟩ => ⟨not_frozen_none _, matched, (innerNormalA_iff program context inner).mpr normal⟩⟩

variable [Fintype ι] [DecidableEq ι]

/-- **One leftmost-innermost firing is one leftmost-innermost reduction, both ways.** -/
theorem leftmost_step_iff (state : State (strategyProgram program)) (call : Term sig Γ .term)
    (determined : Determines (strategyProgram program) state call) (answer : Term sig Γ .term) :
    (∃ (key : InnermostKey Γ ι) (_ : Clear program key.2.1) (valid : InnermostAdmitted program state key),
        Reads (strategyProgram program) (innermostDestination program state key valid) answer) ↔
      LeftmostInnermost (noDeclarations (Var Γ .term)) program call answer := by
  constructor
  · rintro ⟨⟨Δ, context, index, bound⟩, clear, valid, Future, future, solution, reads⟩
    obtain ⟨inner, rfl, ⟨θ, matched⟩, normal, _⟩ :=
      (innermost_admitted_iff program state _ determined ⟨Δ, context, index, bound⟩).mp valid
    have answered := (reads_iff state _ determined _ valid.toPlain answer).mp
      ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution answer).mp reads⟩
    obtain ⟨other, result, same, rfl, branch⟩ := (atContext_answers (grammar := grammar) context _ _ answer).mp answered
    rw [← plug_source_injective context same] at branch
    exact ⟨Δ, context, index, inner, result,
      leftmost_iff_clear.mpr ⟨rfl, clear, (innermostAt_none_iff program context inner).mpr ⟨⟨index, θ, matched⟩, normal⟩⟩,
      rfl, branch⟩
  · rintro ⟨Δ, context, index, inner, result, leftmost, rfl, answered⟩
    obtain ⟨rfl, clear, innermost⟩ := leftmost_iff_clear.mp leftmost
    obtain ⟨-, normal⟩ := (innermostAt_none_iff program context inner).mp innermost
    obtain ⟨θ, matched, _⟩ := answered
    have valid := (innermost_admitted_iff program state _ determined ⟨Δ, context, index, termSize inner⟩).mpr
      ⟨inner, rfl, ⟨θ, matched⟩, normal, bounded_size inner⟩
    refine ⟨⟨Δ, context, index, termSize inner⟩, clear, valid, ?_⟩
    obtain ⟨Future, future, solution, reads⟩ := (reads_iff state _ determined _ valid.toPlain _).mpr
      ((atContext_answers (grammar := grammar) context _ _ _).mpr ⟨inner, result, rfl, rfl, θ, matched, by assumption⟩)
    exact ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution _).mpr reads⟩

/-! ## With `atom` declarations -/

/-- **Soundness with declarations.** A firing at a key that is clear and evaluated under the
declarations is a leftmost-innermost reduction with those declarations: the step's checks refute
every match strictly inside the redex, frozen positions included, which is more than the reference
asks. -/
theorem leftmost_step_sound_atoms (decl : Declarations (Var Γ .term)) (state : State (strategyProgram program))
    (call : Term sig Γ .term) (determined : Determines (strategyProgram program) state call) (answer : Term sig Γ .term)
    (fired : ∃ (key : InnermostKey Γ ι) (_ : LeftClear decl program some key.2.1) (_ : ¬ Frozen decl some key.2.1)
      (valid : InnermostAdmitted program state key),
        Reads (strategyProgram program) (innermostDestination program state key valid) answer) :
    LeftmostInnermost decl program call answer := by
  obtain ⟨⟨Δ, context, index, bound⟩, clear, live, valid, Future, future, solution, reads⟩ := fired
  obtain ⟨inner, rfl, ⟨θ, matched⟩, normal, _⟩ :=
    (innermost_admitted_iff program state _ determined ⟨Δ, context, index, bound⟩).mp valid
  have answered := (reads_iff state _ determined _ valid.toPlain answer).mp
    ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution answer).mp reads⟩
  obtain ⟨other, result, same, rfl, branch⟩ := (atContext_answers (grammar := grammar) context _ _ answer).mp answered
  rw [← plug_source_injective context same] at branch
  have normalA : InnerNormalA decl program some context inner :=
    fun below term positive isInner _ => normal below term positive isInner
  exact ⟨Δ, context, index, inner, result,
    leftmost_iff_clear.mpr ⟨rfl, clear, live, ⟨index, θ, matched⟩, normalA⟩, rfl, branch⟩

/-- **Completeness with declarations, where no frozen position inside the redex matches.** A
leftmost-innermost reduction whose redex has no match strictly inside, frozen positions included, is
one firing at a clear, evaluated key. -/
theorem leftmost_step_complete_atoms (decl : Declarations (Var Γ .term)) (state : State (strategyProgram program))
    {Δ : Ctx sig} {context : Context Γ Δ} {index : ι} {inner result : Term sig Δ .term}
    (determined : Determines (strategyProgram program) state (context.plug inner))
    (leftmost : LeftmostAt decl program some (context.plug inner) context inner)
    (answered : Answers (raiseAt context (program index)) inner result)
    (insideAll : InnerNormal program context inner) :
    ∃ (key : InnermostKey Γ ι) (_ : LeftClear decl program some key.2.1) (_ : ¬ Frozen decl some key.2.1)
      (valid : InnermostAdmitted program state key),
        Reads (strategyProgram program) (innermostDestination program state key valid) (context.plug result) := by
  obtain ⟨-, clear, innermost⟩ := leftmost_iff_clear.mp leftmost
  obtain ⟨θ, matched, _⟩ := answered
  have valid := (innermost_admitted_iff program state _ determined ⟨Δ, context, index, termSize inner⟩).mpr
    ⟨inner, rfl, ⟨θ, matched⟩, insideAll, bounded_size inner⟩
  refine ⟨⟨Δ, context, index, termSize inner⟩, clear, innermost.1, valid, ?_⟩
  obtain ⟨Future, future, solution, reads⟩ := (reads_iff state _ determined _ valid.toPlain _).mpr
    ((atContext_answers (grammar := grammar) context _ _ _).mpr ⟨inner, result, rfl, rfl, θ, matched, by assumption⟩)
  exact ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution _).mpr reads⟩

/-! ## Runs -/

/-- **The leftmost-innermost firings**: innermost firings at clear keys. -/
noncomputable def LeftmostTransition (before after : State (strategyProgram program)) : Prop :=
  ∃ (key : InnermostKey Γ ι) (_ : Clear program key.2.1) (valid : InnermostAdmitted program before key),
    after = innermostDestination program before key valid

/-- **Reflection of one firing**, at any state: every reading of its result is a leftmost-innermost
reduction of a reading of the call. -/
theorem leftmost_reflected {before after : State (strategyProgram program)}
    (transition : LeftmostTransition program before after)
    (value : Term (signature sig before.1.declarations) Γ .term) (holds : Holds (strategyProgram program) before value)
    {Future : Type} {future : Future → MetaArity sig} (solution : Assignment after.1.declarations future)
    (answer : Term sig Γ .term) (reads : ReadsAt (strategyProgram program) after solution answer) :
    ∃ (old : Assignment before.1.declarations (ground sig)) (call : Term sig Γ .term),
      ReadsAt (strategyProgram program) before old call ∧
        LeftmostInnermost (noDeclarations (Var Γ .term)) program call answer := by
  obtain ⟨⟨Δ, context, index, bound⟩, clear, valid, rfl⟩ := transition
  obtain ⟨old, call, readsCall, answered⟩ := destination_reflected before _ valid.toPlain value holds solution answer
    ((guarded_reads_as_plain before _ _ valid solution answer).mp reads)
  have absent : CarriersAbsent (strategyProgram program) before (fireOf ⟨Δ, context, index, bound⟩)
      (carriersOf ⟨Δ, context, index, bound⟩) :=
    ((guarded_admitted_iff before value holds _ _ (fire_apart _)).mp valid).2
  obtain ⟨θ, matched, read⟩ := answered
  have free := absent (ground sig) old call readsCall θ matched
  obtain ⟨inner, result, rfl, rfl, branch⟩ :=
    (atContext_answers (grammar := grammar) context _ call answer).mp ⟨θ, matched, read⟩
  have normal : InnerNormal program context inner := ((carriers_absent_at_iff program context index bound inner).mp free).1
  obtain ⟨θ', matched', _⟩ := id branch
  exact ⟨old, _, readsCall, Δ, context, index, inner, result,
    leftmost_iff_clear.mpr ⟨rfl, clear, (innermostAt_none_iff program context inner).mpr ⟨⟨index, θ', matched'⟩, normal⟩⟩,
    rfl, branch⟩

/-- Every reading after a run of leftmost-innermost firings is reached by leftmost-innermost
reduction. -/
theorem leftmost_runs_backward {call : Term sig Γ .term} {after : State (strategyProgram program)}
    (path : Relation.ReflTransGen (LeftmostTransition program) (initial call) after) :
    (∃ value, Holds (strategyProgram program) after value) ∧
      ∀ answer, Reads (strategyProgram program) after answer →
        Relation.ReflTransGen (LeftmostInnermost (noDeclarations (Var Γ .term)) program) call answer := by
  induction path with
  | refl =>
      refine ⟨⟨_, initial_holds call⟩, ?_⟩
      rintro answer ⟨Future, future, solution, reads⟩
      obtain rfl := (initial_determines call).2 future solution answer reads
      exact .refl
  | tail _ transition ih =>
      obtain ⟨⟨value, holds⟩, earlier⟩ := ih
      refine ⟨?_, ?_⟩
      · obtain ⟨key, _, valid, rfl⟩ := transition
        exact ⟨_, (guarded_holds_as_plain _ _ _ valid _).mpr (destination_holds _ _ valid.toPlain holds.1)⟩
      · rintro answer ⟨Future, future, solution, reads⟩
        obtain ⟨old, middle, readsMiddle, step⟩ := leftmost_reflected program transition value holds solution answer reads
        exact (earlier middle ⟨_, _, old, readsMiddle⟩).tail step

/-- For determinate equations, every leftmost-innermost run is a run of leftmost-innermost firings
that fixes its answer. -/
theorem leftmost_runs_fixes
    (determinate : ∀ {Δ : Ctx sig} (context : Context Γ Δ) (index : ι), Determinate (raiseAt context (program index)))
    {call answer : Term sig Γ .term}
    (runs : Relation.ReflTransGen (LeftmostInnermost (noDeclarations (Var Γ .term)) program) call answer) :
    ∃ after, Relation.ReflTransGen (LeftmostTransition program) (initial call) after ∧
      Fixes (strategyProgram program) after answer := by
  induction runs with
  | refl => exact ⟨initial call, .refl, initial_fixes call⟩
  | tail _ step ih =>
      obtain ⟨middle, path, fixes⟩ := ih
      obtain ⟨Δ, context, index, inner, result, leftmost, isAnswer, answered⟩ := step
      obtain ⟨isCall, clear, innermost⟩ := leftmost_iff_clear.mp leftmost
      obtain ⟨-, normal⟩ := (innermostAt_none_iff program context inner).mp innermost
      obtain ⟨θ, matched, _⟩ := id answered
      subst isCall
      have valid := (innermost_admitted_iff program middle _ fixes.determines ⟨Δ, context, index, termSize inner⟩).mpr
        ⟨inner, rfl, ⟨θ, matched⟩, normal, bounded_size inner⟩
      obtain ⟨next, nextAnswers, nextFixes⟩ := fixes_destination middle _ fixes _ valid.toPlain
        (atContext_determinate grammar context _ (determinate context index))
      have same := Determinate.answer_unique (atContext_determinate grammar context _ (determinate context index))
        nextAnswers ((atContext_answers (grammar := grammar) context _ _ _).mpr ⟨inner, result, rfl, isAnswer, answered⟩)
      subst same
      exact ⟨_, path.tail ⟨⟨Δ, context, index, termSize inner⟩, clear, valid, rfl⟩, nextFixes⟩

/-- **Adequacy of leftmost-innermost reduction under binders, on the step.** For determinate
equations, leftmost-innermost reduction reaches exactly the readings of runs of leftmost-innermost
firings. -/
theorem leftmost_execution_iff
    (determinate : ∀ {Δ : Ctx sig} (context : Context Γ Δ) (index : ι), Determinate (raiseAt context (program index)))
    (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (LeftmostInnermost (noDeclarations (Var Γ .term)) program) call answer ↔
      ∃ after, Relation.ReflTransGen (LeftmostTransition program) (initial call) after ∧
        Reads (strategyProgram program) after answer := by
  constructor
  · intro runs
    obtain ⟨after, path, fixes⟩ := leftmost_runs_fixes program determinate runs
    exact ⟨after, path, fixes.determines.1⟩
  · rintro ⟨after, path, reads⟩
    exact (leftmost_runs_backward program path).2 answer reads

#print axioms innermostAt_none_iff
#print axioms leftmost_step_iff
#print axioms leftmost_step_sound_atoms
#print axioms leftmost_step_complete_atoms
#print axioms leftmost_reflected
#print axioms leftmost_runs_backward
#print axioms leftmost_runs_fixes
#print axioms leftmost_execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.LeftmostStep
