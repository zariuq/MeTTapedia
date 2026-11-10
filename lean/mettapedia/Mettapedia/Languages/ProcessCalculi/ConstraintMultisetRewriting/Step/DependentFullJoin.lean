import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolver

/-!
# The unconditional fibre join, where the pattern solver decides

R91's fibre join (`fibre_admission_transfer`) holds at every firing whose translated information the
dependent unifier decides in the fibre (`DecidedInFibre`): by a principal answer landing in a
translated telescope, or by a refutation. This module derives that condition from the actual pattern
solver (`ContextualDependentPatternSolver.solver`: the general pattern step for the newest
metavariable with its occurs check, then the worklist round of rigid clashes, typed eta conversion
and newest-variable dispatch with wake-up), run in the actual driver.

**Frames kept by a solver** (`KeepsFrames`, `drive_solved_target`). When every progressing round of a
solver keeps a property of frames, every solved run from a frame with the property ends at a frame
with it.

**The pattern solver's answer frames are prefixes** (`round_target`). Each progressing round keeps
its frame (conversion) or removes the newest declaration (the general pattern step and the
dispatcher). This is read off the solver's definitions, rule by rule (`step_solved_target`,
`tryActive_target`, `searchStore_target`, `patternRule_target`, `dispatchNewest_target`,
`worklist_round_target`).

**Translated telescopes are closed under prefixes** (`translated_base`): a translated telescope
lists the closed types `Π Γ. s` of its metavariables, newest last, so dropping the newest leaves the
telescope of the rest of the list.

**The join is unconditional on the decided fragment** (`decidedInFibre_of_decided`,
`fibre_admission_transfer_of_decided`). On every translated store the pattern solver decides at some
budget, its answer frame is a translated telescope or its answer is a refutation, so `DecidedInFibre`
holds, and admission through the fibre is the dependent admission condition on the translated data.
The fragment is the solver's own: no store is assumed to have translated answer frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFibre Translation
open ContextualDependentUpdate

/-! ## Frames kept by a solver -/

section Driver

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A solver keeps a property of frames** when every progressing round from a frame with the
property reports an update whose target has it. -/
def KeepsFrames (solver : ContextualDependentWorklist.Solver levels) (P : Context rules → Prop) : Prop :=
  ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} {update : Update levels problem}
    {smaller : ContextualDependentWorklist.Below (solver.rank update.remaining) (solver.rank problem)},
    solver.round problem = .progress update smaller → P Γ → P update.target

theorem advance_done_solved (solver : ContextualDependentWorklist.Solver levels) {Γ : Context rules}
    {original : EquationStore (TotalTerm Γ)} {start state : Update levels original}
    {finished : state.remaining = []}
    (ended : ContextualDependentWorklist.advance solver start = .done (.solved state finished)) :
    state = start := by
  unfold ContextualDependentWorklist.advance at ended
  split at ended
  · cases ended
    rfl
  · split at ended <;> cases ended

/-- **A solved run ends at a frame with every property its solver keeps.** -/
theorem drive_solved_target (solver : ContextualDependentWorklist.Solver levels) {P : Context rules → Prop}
    (keeps : KeepsFrames solver P) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} :
    ∀ (fuel : Nat) (start : Update levels original), P start.target →
      ∀ {state : Update levels original} {finished : state.remaining = []},
        ContextualDependentWorklist.drive solver fuel start = .solved state finished → P state.target
  | 0, _, _, _, _, solved => by cases solved
  | fuel + 1, start, holds, state, finished, solved => by
      rw [ContextualDependentWorklist.drive_succ] at solved
      cases decided : ContextualDependentWorklist.advance solver start with
      | done outcome =>
          rw [decided] at solved
          have same : outcome = .solved state finished := solved
          subst same
          rw [advance_done_solved solver decided]
          exact holds
      | next next =>
          rw [decided] at solved
          obtain ⟨update, smaller, progressed, rfl⟩ :=
            ContextualDependentWorklist.advance_next_progress solver decided
          have next : P update.target := keeps progressed holds
          exact drive_solved_target solver keeps fuel (start.then update) next
            (show ContextualDependentWorklist.drive solver fuel (start.then update) = _ from solved)

end Driver

/-! ## Translated telescopes -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

/-- **A translated telescope**: the image of a list frame. -/
def Translated (Γ : Context S.R) : Prop :=
  ∃ N : List (Binding.MetaArity sig), Γ = (fibre facts roots heads church names realization).obj N

theorem translated_obj (M : List (Binding.MetaArity sig)) :
    Translated facts roots heads church names realization
      ((fibre facts roots heads church names realization).obj M) :=
  ⟨M, rfl⟩

/-- **Dropping the newest declaration of a translated telescope leaves a translated telescope.** -/
theorem translated_prefix {n : Nat} {raw : Ctx Head n} {code : Tm Head n}
    {formed : CtxFormed S.R (.snoc raw code)}
    (translated : Translated facts roots heads church names realization ⟨n + 1, .snoc raw code, formed⟩) :
    Translated facts roots heads church names realization
      ⟨n, raw, ContextualDependentWorklist.formedPrefix formed⟩ := by
  obtain ⟨N, same⟩ := translated
  cases N with
  | nil => exact absurd (congrArg Context.arity same) (Nat.succ_ne_zero n)
  | cons a N =>
      refine ⟨N, ?_⟩
      have arity : n + 1 = N.length + 1 := congrArg Context.arity same
      obtain rfl : n = N.length := Nat.succ.inj arity
      have raws : HEq (Ctx.snoc raw code)
          (Ctx.snoc (metaCtx (Head := Head) names N)
            (liftClosed (BindingSignatureEmbedding.bindingType names a.1 a.2))) :=
        congr_arg_heq Context.raw same
      obtain ⟨rfl, -⟩ := Ctx.snoc.inj (eq_of_heq raws)
      rfl

/-- **The base of a translated telescope's newest declaration is translated.** -/
theorem translated_base {Γ : Context S.R} (view : ContextualDependentWorklist.Newest Γ)
    (translated : Translated facts roots heads church names realization Γ) :
    Translated facts roots heads church names realization view.base := by
  obtain ⟨base, type, same⟩ := view
  subst same
  exact translated_prefix facts roots heads church names realization
    (n := base.arity) (raw := base.raw) (code := type.code) (formed := (extend base type).formed) translated

/-! ## The pattern solver removes only newest declarations -/

section Rules

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))

open ContextualDependentPiSpine ContextualDependentGeneralPattern in
/-- **A solved general-pattern step defines the newest metavariable**: its answer frame is the
base. -/
theorem step_solved_target
    (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
    (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
    {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    {result : ContextualDependentScopedDispatch.Result S.levels [pattern.constraint right]}
    {finished : result.update.remaining = []}
    (solved : Pattern.step facts roots heads algebra declared reflects complete rigid normalizes certifyNormal
      choices reducer fuel pattern right = .solved result finished) :
    result.update.target = Γ := by
  unfold Pattern.step at solved
  split at solved
  · cases solved
    rfl
  · unfold Pattern.tryRefute at solved
    split at solved
    · cases solved
    · split at solved
      · cases solved
      · split at solved <;> cases solved

/-- **A solved pattern attempt on one equation removes the newest declaration.** -/
theorem tryActive_target (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    {scopeType : TypeOver (extend Γ type)} {scope : ContextualDependentPiSpine.Spine scopeType}
    {active : ContextualDependentScope.Active scope.target} {equation : Equation (TotalTerm (extend Γ type))}
    {view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    {rest : EquationStore (TotalTerm (extend Γ type))} {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < (extend Γ type).arity}
    (solved : ContextualDependentPatternSolver.tryActive rigid facts complete roots heads algebra declared choices
      reducer normalizes certifyNormal fuel type scope active equation view rest = some (.solved update smaller)) :
    update.target = Γ := by
  unfold ContextualDependentPatternSolver.tryActive at solved
  split at solved
  · cases solved
  · split at solved
    · cases solved
    · split at solved
      · cases solved
      · split at solved
        · rename_i result finished computed
          simp only at solved
          split at solved
          · cases solved
            exact step_solved_target facts roots heads rigid complete algebra declared choices reducer normalizes
              certifyNormal _ fuel _ _ computed
          · cases solved
        · cases solved
        · simp only at solved
          split at solved <;> cases solved

theorem tryEquation_target (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type)))
    {update : Update S.levels (equation :: rest)} {smaller : update.target.arity < (extend Γ type).arity}
    (solved : ContextualDependentPatternSolver.tryEquation rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel type equation rest = some (.solved update smaller)) :
    update.target = Γ := by
  unfold ContextualDependentPatternSolver.tryEquation at solved
  split at solved
  · cases solved
  · rename_i scope active view _
    split at solved
    · rename_i found computed
      cases solved
      exact tryActive_target facts roots heads rigid complete algebra declared choices reducer normalizes
        certifyNormal fuel type computed
    · exact tryActive_target facts roots heads rigid complete algebra declared choices reducer normalizes
        certifyNormal fuel type (view := fun solution =>
          (view solution).trans (ContextualDependentPatternSolver.toScoped_swap scope active solution).symm) solved

theorem searchStore_target (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))) {update : Update S.levels problem}
      {smaller : update.target.arity < (extend Γ type).arity},
      ContextualDependentPatternSolver.searchStore rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel type problem = some (.solved update smaller) →
      update.target = Γ
  | [], _, _, solved => by simp [ContextualDependentPatternSolver.searchStore] at solved
  | equation :: rest, update, smaller, solved => by
      simp only [ContextualDependentPatternSolver.searchStore] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact tryEquation_target facts roots heads rigid complete algebra declared choices reducer root normalizes
          certifyNormal fuel type equation rest computed
      · obtain ⟨found, computed, kept⟩ := Option.map_eq_some_iff.mp solved
        cases found with
        | solved inner innerSmaller =>
            cases kept
            exact searchStore_target fuel type rest computed
        | refuted _ => cases kept

/-- **A solved pattern rule removes the newest declaration.** -/
theorem patternRule_target (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPatternSolver.patternRule rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = some (.solved update smaller)) :
    ∃ view : ContextualDependentWorklist.Newest Θ, update.target = view.base := by
  unfold ContextualDependentPatternSolver.patternRule at solved
  split at solved
  · cases solved
  · rename_i view _
    refine ⟨view, ?_⟩
    obtain ⟨base, type, same⟩ := view
    subst same
    exact searchStore_target facts roots heads rigid complete algebra declared choices reducer root normalizes
      certifyNormal fuel type problem solved

/-- **A successful dispatch removes the newest declaration.** -/
theorem dispatchNewest_target (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    {found : {update : Update S.levels problem // update.target.arity < Γ.arity + 1}}
    (computed : ContextualDependentWorklist.dispatchNewest facts roots heads algebra declared choices reducer fuel
      type problem = some found) :
    found.1.target = Γ := by
  unfold ContextualDependentWorklist.dispatchNewest at computed
  split at computed
  · cases computed
  · rename_i updated accepted
    cases computed
    exact ContextualDependentDispatch.search_target facts roots heads algebra declared choices reducer type problem
      updated accepted

/-- **A progressing worklist round keeps the frame or removes the newest declaration.** -/
theorem worklist_round_target (fuel : Nat) {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size update.remaining)
      (ContextualDependentWorklist.size problem)}
    (progressed : ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices
      reducer fuel problem = .progress update smaller) :
    update.target = Γ ∨ ∃ view : ContextualDependentWorklist.Newest Γ, update.target = view.base := by
  unfold ContextualDependentWorklist.round at progressed
  split at progressed
  · cases progressed
  · split at progressed
    · cases progressed
      exact .inl rfl
    · split at progressed
      · cases progressed
      · rename_i view _
        split at progressed
        · cases progressed
        · rename_i u s computed
          cases progressed
          refine .inr ⟨view, ?_⟩
          obtain ⟨base, type, same⟩ := view
          subst same
          exact dispatchNewest_target facts roots heads algebra declared choices reducer fuel type problem computed

/-- **Every progressing round of the pattern solver keeps the frame or removes the newest
declaration.** -/
theorem round_target (fuel : Nat) {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size update.remaining)
      (ContextualDependentWorklist.size problem)}
    (progressed : ContextualDependentPatternSolver.round rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = .progress update smaller) :
    update.target = Γ ∨ ∃ view : ContextualDependentWorklist.Newest Γ, update.target = view.base := by
  unfold ContextualDependentPatternSolver.round at progressed
  split at progressed
  · rename_i u s computed
    cases progressed
    exact .inr (patternRule_target facts roots heads rigid complete algebra declared choices reducer root normalizes
      certifyNormal fuel problem computed)
  · cases progressed
  · exact worklist_round_target facts roots heads rigid complete algebra declared choices reducer fuel progressed

/-- **The pattern solver keeps translated telescopes.** -/
theorem keeps_translated (fuel : Nat) :
    KeepsFrames (ContextualDependentPatternSolver.solver rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel) (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  rcases round_target facts roots heads rigid complete algebra declared choices reducer root normalizes certifyNormal
      fuel progressed with same | ⟨view, same⟩
  · rw [same]
    exact translated
  · rw [same]
    exact translated_base facts roots heads church names realization view translated

/-! ## The join, where the pattern solver decides -/

/-- **The pattern solver's decision is a decision in the fibre.** On a translated store, a solved
run of the actual pattern solver ends at a translated telescope with a principal answer, and a
refuted run refutes the store. -/
theorem decidedInFibre_of_decided {M : List (Binding.MetaArity sig)}
    (K : EquationStore (Binding.ContextualFamily.Observation sig M.get)) (rounds fuel : Nat)
    (decided : (ContextualDependentWorklist.run (ContextualDependentPatternSolver.solver rigid facts complete roots
      heads algebra declared choices reducer root normalizes certifyNormal rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K := by
  generalize computed : ContextualDependentWorklist.run (ContextualDependentPatternSolver.solver rigid facts complete
      roots heads algebra declared choices reducer root normalizes certifyNormal rounds)
      ((fibre facts roots heads church names realization).store K) fuel = outcome at decided
  cases outcome with
  | solved state finished =>
      have principal := ContextualDependentWorklist.drive_solved_principal _ computed
      obtain ⟨N, same⟩ := drive_solved_target _
        (keeps_translated facts roots heads church names realization rigid complete algebra declared choices reducer
          root normalizes certifyNormal rounds)
        fuel _ (translated_obj facts roots heads church names realization M) computed
      have landing : ∀ (T : Context S.R) (answer : T ⟶ (fibre facts roots heads church names realization).obj M),
          T = (fibre facts roots heads church names realization).obj N →
          (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) answer →
          DecidedInFibre facts roots heads church names realization K := by
        intro T answer same principal
        subst same
        exact .inl ⟨N, answer, principal⟩
      exact landing _ state.answer same principal
  | refuted absent => exact .inr absent
  | stuck _ => exact False.elim decided
  | cutoff _ => exact False.elim decided

/-- **The fibre join is unconditional where the pattern solver decides.** For every candidate step
over the second-order frames whose guards and predicate queries are equation guards, at a firing
whose translated information the actual pattern solver decides at some budget, admission is the
dependent admission condition on the translated data. -/
theorem fibre_admission_transfer_of_decided
    (sortInjective : Function.Injective names.sort)
    (closed : ClosedRealization (S := S) names)
    (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
    {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
    (P : Step (listFrames sig) O State Firing) [P.Guarded]
    (guards : ∀ {s : State} (f : Firing s),
      EquationStore (Binding.ContextualFamily.Observation sig (P.target f).get))
    (holds : ∀ {s : State} (f : Firing s) (N : List (Binding.MetaArity sig))
      (g : Binding.ContextualFamily.Assignment (S := sig) (P.target f).get N.get),
      P.Holds f N g ↔ (listFrames sig).Models g (guards f))
    {s : State} (f : Firing s) (rounds fuel : Nat)
    (decided : (ContextualDependentWorklist.run (ContextualDependentPatternSolver.solver rigid facts complete roots
      heads algebra declared choices reducer root normalizes certifyNormal rounds)
      ((fibre facts roots heads church names realization).store (P.information f)) fuel).Decided) :
    P.Admits f ↔ P.Shapes f ∧
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ())
        (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
        (P.information f)) ∧
      (frames S.levels).Entails ((fibre facts roots heads church names realization).store
          (P.information f))
        (fun _ g => (frames S.levels).Models g
          ((fibre facts roots heads church names realization).store (guards f))) :=
  fibre_admission_transfer facts roots heads algebra complete rigid church names realization sortInjective closed
    @operatorInjective P guards holds f
    (decidedInFibre_of_decided facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal (P.information f) rounds fuel decided)

end Rules

end DependentFull

#print axioms DependentFull.advance_done_solved
#print axioms DependentFull.drive_solved_target
#print axioms DependentFull.translated_prefix
#print axioms DependentFull.translated_base
#print axioms DependentFull.step_solved_target
#print axioms DependentFull.tryActive_target
#print axioms DependentFull.tryEquation_target
#print axioms DependentFull.searchStore_target
#print axioms DependentFull.patternRule_target
#print axioms DependentFull.dispatchNewest_target
#print axioms DependentFull.worklist_round_target
#print axioms DependentFull.round_target
#print axioms DependentFull.keeps_translated
#print axioms DependentFull.decidedInFibre_of_decided
#print axioms DependentFull.fibre_admission_transfer_of_decided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
