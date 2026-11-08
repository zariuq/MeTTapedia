import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStrategyPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersAbsence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersCached
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersSolvers

/-!
# Innermost reduction under binders

**The strategy.** An equation fires at a position only when no equation matches strictly inside the
redex. Positions are λ contexts, under binders too, and a root equation is raised along the binders
its position passes (R98's `raiseAt`).

**The reference semantics** (`Innermost`) is reduction in λ contexts restricted to that strategy. It
is defined from source plugging and `Matches` alone (`InnerNormal`).

**On the step**, an innermost firing is one guarded firing (`ProgramBindersAbsenceGuards`) of the
plugged equation `(= C[lhs] C[rhs])`, keyed by the context `C`, the equation and a depth `bound`:
- one absence carrier per path of length `1 … bound` below `C` and per equation: the equation, raised
  along the path's binders, at the end of the path, with every sibling a fresh hole;
- one absence carrier per path of length `bound + 1` below `C`: "some term is there".
Each carrier is an existing `.absent` guard asked over every future solution, so the decision is the
certified refutation of `ProgramBindersAbsenceGuards` (`ProgramBindersStrategyDecision`). A firing is admitted exactly when the redex matches, nothing strictly inside it is
matched, and it has no position deeper than `bound` (`innermost_admitted_iff`); the size of the redex is
always a large enough bound.

- `innermost_reflected`: every innermost firing reads only innermost reductions of its readings.
- `innermost_execution_iff`: for determinate equations, innermost runs of the reference reach exactly the
  readings of runs of innermost firings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ContextualPatternFragment (Pattern generator_pattern instantiate_preserves)
open Nested (raiseAt raisedSchema grammar)

variable {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term)

/-! ## The reference semantics -/

/-- Some equation, raised along the position's binders, matches the subterm at the position. -/
def MatchesAt {Δ : Ctx sig} (context : Context Γ Δ) (term : Term sig Δ .term) : Prop :=
  ∃ index θ, Matches (raiseAt context (program index)) term θ

/-- No equation matches strictly inside the redex `inner` at position `context`. -/
def InnerNormal {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) : Prop :=
  ∀ {Θ : Ctx sig} (below : Context Δ Θ) (term : Term sig Θ .term), 0 < depth below → inner = below.plug term →
    ¬ MatchesAt program (comp context below) term

/-- **Innermost reduction in λ contexts.** -/
def Innermost (call answer : Term sig Γ .term) : Prop :=
  ∃ (Δ : Ctx sig) (context : Context Γ Δ) (index : ι) (inner result : Term sig Δ .term),
    call = context.plug inner ∧ answer = context.plug result ∧ Answers (raiseAt context (program index)) inner result ∧
      InnerNormal program context inner

/-- Innermost reduction is a restriction of reduction in λ contexts. -/
theorem innermost_reduces {call answer : Term sig Γ .term} (step : Innermost program call answer) :
    CRewrites grammar (raisedSchema program) call answer := by
  obtain ⟨Δ, context, index, inner, result, isCall, isAnswer, answered, _⟩ := step
  exact ⟨Δ, context, index, inner, result, isCall, isAnswer, answered⟩

/-- Every position of `inner` is at most `bound` deep. -/
def Bounded {Δ : Ctx sig} (bound : Nat) (inner : Term sig Δ .term) : Prop :=
  ∀ {Θ : Ctx sig} (path : Path Δ Θ) (siblings : (index : Nat) → Term sig (path.siblingContext index) .term)
    (term : Term sig Θ .term), inner = path.fillSource siblings term → path.length ≤ bound

theorem bounded_size {Δ : Ctx sig} (inner : Term sig Δ .term) : Bounded (termSize inner) inner := by
  intro Θ path siblings term same
  have bound := Path.length_lt_size path siblings term
  rw [← same] at bound
  omega

theorem plug_source_injective {Δ : Ctx sig} (context : Context Γ Δ) {first second : Term sig Δ .term}
    (same : context.plug first = context.plug second) : first = second := by
  induction context with
  | hole => exact same
  | appLeft inner argument ih => exact ih (Controls.appT_inj same).1
  | appRight function inner ih => exact ih (Controls.appT_inj same).2
  | underLam inner ih => exact ih (Controls.lamT_inj same)

/-! ## Patterns along a path -/

/-- The holes of a pattern along a path: one per sibling, and the target's. -/
abbrev pathArity {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term) :
    Nat ⊕ target.Holes → MetaArity sig :=
  Sum.elim (fun index => (path.siblingContext index, .term)) target.arity

/-- The target's left-hand side at the end of the path, every sibling a fresh hole. -/
def pathLhs {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term) :
    Term (signature sig (pathArity path target)) Δ .term :=
  path.fill (pathArity path target) (fun index => generator (pathArity path target) (.inl index))
    (instantiate (fun hole => generator (pathArity path target) (.inr hole)) target.lhs)

/-- "The target matches at the end of the path", as an equation whose left-hand side is a pattern. -/
def pathEquation {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term) : Equation sig Δ .term :=
  ⟨Nat ⊕ target.Holes, by letI := target.holesEq; infer_instance, pathArity path target, pathLhs path target,
    pathLhs path target⟩

/-- A ground solution from siblings and a solution of the target. -/
def pathGround {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term)
    (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (θ : target.Ground) :
    (pathEquation path target).Ground :=
  fun hole => Sum.rec (motive := fun hole => Term sig (pathArity path target hole).1 (pathArity path target hole).2)
    siblings θ hole

theorem pathEquation_matches_iff {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term)
    (term : Term sig Δ .term) :
    (∃ θ, Matches (pathEquation path target) term θ) ↔
      ∃ (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (position : Term sig Θ .term),
        term = path.fillSource siblings position ∧ ∃ θ, Matches target position θ := by
  constructor
  · rintro ⟨θ, matched⟩
    have expanded := (Path.instantiate_fill ((pathEquation path target).assign θ (ground sig)) path
      (fun index => generator (pathArity path target) (.inl index))
      (instantiate (fun hole => generator (pathArity path target) (.inr hole)) target.lhs)).symm.trans matched
    obtain ⟨siblings, position, rfl, positionSame⟩ := Path.fill_recovers path _ _ term expanded
    refine ⟨siblings, position, rfl, fun hole => θ (.inr hole), ?_⟩
    have same : Assignment.compose ((pathEquation path target).assign θ (ground sig))
        (fun hole => generator (pathArity path target) (.inr hole)) = target.assign (fun hole => θ (.inr hole)) (ground sig) := by
      funext hole
      exact instantiate_generator _ _
    exact (congrArg (fun assignment => instantiate assignment target.lhs) same.symm).trans
      ((Assignment.instantiate_compose _ _ _).trans positionSame)
  · rintro ⟨siblings, position, rfl, θ, matched⟩
    refine ⟨pathGround path target siblings θ, ?_⟩
    have same : Assignment.compose ((pathEquation path target).assign (pathGround path target siblings θ) (ground sig))
        (fun hole => generator (pathArity path target) (.inr hole)) = target.assign θ (ground sig) := by
      funext hole
      exact instantiate_generator _ _
    have siblingsSame : (fun index => instantiate ((pathEquation path target).assign (pathGround path target siblings θ)
        (ground sig)) (generator (pathArity path target) (.inl index))) =
          fun index => Rigid.includeTerm (ground sig) (siblings index) := by
      funext index
      exact instantiate_generator _ _
    have termSame : instantiate ((pathEquation path target).assign (pathGround path target siblings θ) (ground sig))
        (instantiate (fun hole => generator (pathArity path target) (.inr hole)) target.lhs) =
          Rigid.includeTerm (ground sig) position :=
      (Assignment.instantiate_compose _ _ _).symm.trans
        ((congrArg (fun assignment => instantiate assignment target.lhs) same).trans matched)
    exact (Path.instantiate_fill _ path _ _).trans
      ((congrArg₂ (Path.fill (ground sig) path) siblingsSame termSame).trans (Path.fill_include path siblings position))

theorem pathEquation_pattern {Δ Θ : Ctx sig} (path : Path Δ Θ) (target : Equation sig Θ .term)
    (patterned : Pattern sig target.arity target.lhs) :
    Pattern sig (pathEquation path target).arity (pathEquation path target).lhs :=
  Path.fill_pattern path _ _ (fun _ => generator_pattern _)
    (instantiate_preserves _ (fun _ => generator_pattern _) _ patterned)

/-! ## The program on the step -/

/-- Firing keys: a position and an equation. -/
abbrev FireKey (Γ : Ctx sig) (ι : Type) := Σ Δ : Ctx sig, Context Γ Δ × ι

/-- Carrier keys: a position, a path below it, and an equation or "any term". -/
abbrev CheckKey (Γ : Ctx sig) (ι : Type) := Σ Δ : Ctx sig, Context Γ Δ × (Σ Θ : Ctx sig, Path Δ Θ) × Option ι

/-- The equations of the step: the plugged equations, and the carriers of the strategy's checks. -/
def strategyProgram : FireKey Γ ι ⊕ CheckKey Γ ι → Equation sig Γ .term
  | .inl ⟨_, context, index⟩ => atContext grammar context (raiseAt context (program index))
  | .inr ⟨_, context, ⟨Θ, path⟩, none⟩ => atContext grammar context (pathEquation path (returnEquation Θ .term))
  | .inr ⟨_, context, ⟨_, path⟩, some index⟩ =>
      atContext grammar context (pathEquation path (raiseAlong path (raiseAt context (program index))))

instance keyEq [DecidableEq ι] : DecidableEq (FireKey Γ ι ⊕ CheckKey Γ ι) := by
  letI : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)
  letI : DecidableEq (Ctx sig) := inferInstanceAs (DecidableEq (List sig.Srt))
  letI : ∀ Δ : Ctx sig, DecidableEq (Context Γ Δ) := fun _ => Nested.contextDecEq
  letI : ∀ Δ Θ : Ctx sig, DecidableEq (Path Δ Θ) := fun _ _ => pathDecEq
  letI : DecidableEq (FireKey Γ ι) := inferInstanceAs (DecidableEq (Σ Δ : Ctx sig, Context Γ Δ × ι))
  letI : ∀ Δ : Ctx sig, DecidableEq (Σ Θ : Ctx sig, Path Δ Θ) := fun _ => inferInstance
  letI : DecidableEq (CheckKey Γ ι) :=
    inferInstanceAs (DecidableEq (Σ Δ : Ctx sig, Context Γ Δ × (Σ Θ : Ctx sig, Path Δ Θ) × Option ι))
  exact inferInstance

/-- An innermost firing: a position, an equation, and a depth bound. -/
abbrev InnermostKey (Γ : Ctx sig) (ι : Type) := Σ Δ : Ctx sig, Context Γ Δ × ι × Nat

def fireOf (key : InnermostKey Γ ι) : FireKey Γ ι ⊕ CheckKey Γ ι := .inl ⟨key.1, key.2.1, key.2.2.1⟩

/-- The carriers of an innermost firing. -/
noncomputable def carriersOf [Fintype ι] (key : InnermostKey Γ ι) : List (FireKey Γ ι ⊕ CheckKey Γ ι) :=
  ((List.range key.2.2.2).flatMap fun length => (pathsOf (length + 1) key.1).flatMap fun entry =>
      (Finset.univ : Finset ι).toList.map fun index => .inr ⟨key.1, key.2.1, entry, some index⟩) ++
    (pathsOf (key.2.2.2 + 1) key.1).map fun entry => .inr ⟨key.1, key.2.1, entry, none⟩

theorem mem_carriersOf [Fintype ι] (key : InnermostKey Γ ι) (carrier : FireKey Γ ι ⊕ CheckKey Γ ι) :
    carrier ∈ carriersOf key ↔
      (∃ (entry : Σ Θ : Ctx sig, Path key.1 Θ) (index : ι), 0 < entry.2.length ∧ entry.2.length ≤ key.2.2.2 ∧
          carrier = .inr ⟨key.1, key.2.1, entry, some index⟩) ∨
        ∃ entry : Σ Θ : Ctx sig, Path key.1 Θ, entry.2.length = key.2.2.2 + 1 ∧
          carrier = .inr ⟨key.1, key.2.1, entry, none⟩ := by
  simp only [carriersOf, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨length, short, entry, member, index, rfl⟩ | ⟨entry, member, rfl⟩)
    · have sameLength := length_of_mem_pathsOf _ _ entry member
      exact Or.inl ⟨entry, index, by omega, by omega, rfl⟩
    · exact Or.inr ⟨entry, length_of_mem_pathsOf _ _ entry member, rfl⟩
  · rintro (⟨entry, index, positive, short, rfl⟩ | ⟨entry, sameLength, rfl⟩)
    · refine Or.inl ⟨entry.2.length - 1, by omega, entry, ?_, index, rfl⟩
      have member := mem_pathsOf entry.2
      rwa [show entry.2.length - 1 + 1 = entry.2.length by omega]
    · refine Or.inr ⟨entry, ?_, rfl⟩
      have member := mem_pathsOf entry.2
      rwa [sameLength] at member

theorem fire_apart [Fintype ι] (key : InnermostKey Γ ι) : fireOf key ∉ carriersOf key := by
  intro member
  rcases (mem_carriersOf key (fireOf key)).mp member with ⟨_, _, _, _, impossible⟩ | ⟨_, _, impossible⟩ <;>
    cases impossible

/-! ## Matching the plugged equations -/

theorem atContext_matches_iff {Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Δ .term)
    (call : Term sig Γ .term) :
    (∃ θ, Matches (atContext grammar context e) call θ) ↔
      ∃ inner, call = context.plug inner ∧ ∃ θ, Matches e inner θ := by
  constructor
  · rintro ⟨θ, matched⟩
    obtain ⟨inner, isCall, read⟩ := (atContext_reads (grammar := grammar) context e θ e.lhs call).mp matched
    exact ⟨inner, isCall, θ, read⟩
  · rintro ⟨inner, isCall, θ, matched⟩
    exact ⟨θ, (atContext_reads (grammar := grammar) context e θ e.lhs call).mpr ⟨inner, isCall, matched⟩⟩

/-- **The carriers are absent exactly at innermost redexes of bounded depth.** -/
theorem carriers_absent_at_iff [Fintype ι] {Δ : Ctx sig} (context : Context Γ Δ) (index : ι) (bound : Nat)
    (inner : Term sig Δ .term) :
    (∀ carrier ∈ carriersOf ⟨Δ, context, index, bound⟩, ∀ θ,
        ¬ Matches (strategyProgram program carrier) (context.plug inner) θ) ↔
      InnerNormal program context inner ∧ Bounded bound inner := by
  have atPosition : ∀ {Θ : Ctx sig} (target : Equation sig Θ .term) (path : Path Δ Θ),
      (∃ θ, Matches (atContext grammar context (pathEquation path target)) (context.plug inner) θ) ↔
        ∃ (siblings : (index : Nat) → Term sig (path.siblingContext index) .term) (position : Term sig Θ .term),
          inner = path.fillSource siblings position ∧ ∃ θ, Matches target position θ := by
    intro Θ target path
    rw [atContext_matches_iff]
    constructor
    · rintro ⟨other, same, matched⟩
      rw [← plug_source_injective context same] at matched
      exact (pathEquation_matches_iff path target inner).mp matched
    · intro matched
      exact ⟨inner, rfl, (pathEquation_matches_iff path target inner).mpr matched⟩
  have bounded : (∀ carrier ∈ carriersOf ⟨Δ, context, index, bound⟩, ∀ θ,
      ¬ Matches (strategyProgram program carrier) (context.plug inner) θ) → Bounded bound inner := by
    intro absent Θ path siblings term same
    by_contra deep
    obtain ⟨Θ', shorter, others, rest, sameLength, shorterSame⟩ :=
      Path.prefix_of_path path siblings term (bound + 1) (by omega)
    obtain ⟨θ, matched⟩ := (atPosition (returnEquation Θ' .term) shorter).mpr
      ⟨others, rest, same.trans shorterSame, fun _ => rest, return_matches rest⟩
    exact absent _ ((mem_carriersOf _ _).mpr (Or.inr ⟨⟨Θ', shorter⟩, sameLength, rfl⟩)) θ matched
  constructor
  · intro absent
    have isBounded : Bounded bound inner := bounded absent
    refine ⟨?_, isBounded⟩
    intro Θ below term positive same ⟨other, θ, matched⟩
    have raised : ∃ θ, Matches (raiseAt (comp context below) (program other)) term θ := ⟨θ, matched⟩
    rw [raiseAt_comp, raiseAt_eq_raiseAlong] at raised
    obtain ⟨θ, matched⟩ := raised
    rw [plug_eq_fillSource] at same
    have short := isBounded (contextPath below) (contextSiblings below) term same
    obtain ⟨θ', carried⟩ := (atPosition (raiseAlong (contextPath below) (raiseAt context (program other)))
      (contextPath below)).mpr ⟨contextSiblings below, term, same, θ, matched⟩
    exact absent _ ((mem_carriersOf _ _).mpr (Or.inl ⟨⟨Θ, contextPath below⟩, other,
      by rw [toPath_length]; exact positive, short, rfl⟩)) θ' carried
  · rintro ⟨normal, isBounded⟩ carrier member θ matched
    rcases (mem_carriersOf _ _).mp member with ⟨⟨Θ, path⟩, other, positive, _, rfl⟩ | ⟨⟨Θ, path⟩, sameLength, rfl⟩
    · obtain ⟨siblings, position, same, θ', carried⟩ :=
        (atPosition (raiseAlong path (raiseAt context (program other))) path).mp ⟨θ, matched⟩
      apply normal (path.toContext siblings) position (by rw [Path.toContext_depth]; exact positive)
        (same.trans (Path.toContext_plug path siblings position).symm)
      refine ⟨other, ?_⟩
      rw [raiseAt_comp, raiseAt_toContext]
      exact ⟨θ', carried⟩
    · obtain ⟨siblings, position, same, _⟩ := (atPosition (returnEquation Θ .term) path).mp ⟨θ, matched⟩
      have short := isBounded path siblings position same
      change path.length = bound + 1 at sameLength
      omega

/-! ## One firing -/

variable [Fintype ι] [DecidableEq ι]

/-- The guarded firing of an innermost key is admitted. -/
abbrev InnermostAdmitted (state : State (strategyProgram program)) (key : InnermostKey Γ ι) : Prop :=
  GuardedAdmitted (strategyProgram program) state (fireOf key) (carriersOf key)

/-- **Admission is innermost matching.** At a call every solution reads the same way, an innermost
firing is admitted exactly when the call is a redex at the key's position, nothing strictly inside
the redex is matched, and the redex is no deeper than the key's bound. -/
theorem innermost_admitted_iff (state : State (strategyProgram program)) (call : Term sig Γ .term)
    (determined : Determines (strategyProgram program) state call) (key : InnermostKey Γ ι) :
    InnermostAdmitted program state key ↔
      ∃ inner, call = key.2.1.plug inner ∧ (∃ θ, Matches (raiseAt key.2.1 (program key.2.2.1)) inner θ) ∧
        InnerNormal program key.2.1 inner ∧ Bounded key.2.2.2 inner := by
  obtain ⟨Δ, context, index, bound⟩ := key
  refine (guarded_admitted_iff_determined state call determined _ _ (fire_apart _)).trans ?_
  change ((∃ θ, Matches (atContext grammar context (raiseAt context (program index))) call θ) ∧ _) ↔ _
  rw [atContext_matches_iff]
  constructor
  · rintro ⟨⟨inner, rfl, matched⟩, absent⟩
    exact ⟨inner, rfl, matched, (carriers_absent_at_iff program context index bound inner).mp absent⟩
  · rintro ⟨inner, rfl, matched, normal⟩
    exact ⟨⟨inner, rfl, matched⟩, (carriers_absent_at_iff program context index bound inner).mpr normal⟩

/-- The state after an innermost firing. -/
noncomputable abbrev innermostDestination (state : State (strategyProgram program)) (key : InnermostKey Γ ι)
    (valid : InnermostAdmitted program state key) : State (strategyProgram program) :=
  guardedDestination (strategyProgram program) state (fireOf key) (carriersOf key) valid

/-- **One innermost firing is one innermost reduction, both ways.** -/
theorem innermost_step_iff (state : State (strategyProgram program)) (call : Term sig Γ .term)
    (determined : Determines (strategyProgram program) state call) (answer : Term sig Γ .term) :
    (∃ (key : InnermostKey Γ ι) (valid : InnermostAdmitted program state key),
        Reads (strategyProgram program) (innermostDestination program state key valid) answer) ↔
      Innermost program call answer := by
  constructor
  · rintro ⟨⟨Δ, context, index, bound⟩, valid, Future, future, solution, reads⟩
    obtain ⟨inner, rfl, _, normal, _⟩ :=
      (innermost_admitted_iff program state _ determined ⟨Δ, context, index, bound⟩).mp valid
    have answered := (reads_iff state _ determined _ valid.toPlain answer).mp
      ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution answer).mp reads⟩
    obtain ⟨other, result, same, rfl, branch⟩ := (atContext_answers (grammar := grammar) context _ _ answer).mp answered
    rw [← plug_source_injective context same] at branch
    exact ⟨Δ, context, index, inner, result, rfl, rfl, branch, normal⟩
  · rintro ⟨Δ, context, index, inner, result, rfl, rfl, answered, normal⟩
    obtain ⟨θ, matched, _⟩ := answered
    have valid := (innermost_admitted_iff program state _ determined ⟨Δ, context, index, termSize inner⟩).mpr
      ⟨inner, rfl, ⟨θ, matched⟩, normal, bounded_size inner⟩
    refine ⟨⟨Δ, context, index, termSize inner⟩, valid, ?_⟩
    obtain ⟨Future, future, solution, reads⟩ := (reads_iff state _ determined _ valid.toPlain _).mpr
      ((atContext_answers (grammar := grammar) context _ _ _).mpr ⟨inner, result, rfl, rfl, θ, matched, by assumption⟩)
    exact ⟨Future, future, solution, (guarded_reads_as_plain state _ _ valid solution _).mpr reads⟩

/-! ## Runs -/

/-- **The innermost firings.** -/
noncomputable def InnermostTransition (before after : State (strategyProgram program)) : Prop :=
  ∃ (key : InnermostKey Γ ι) (valid : InnermostAdmitted program before key),
    after = innermostDestination program before key valid

/-- **Reflection of one firing**, at any state: every reading of its result is an innermost reduction
of a reading of the call. -/
theorem innermost_reflected {before after : State (strategyProgram program)}
    (transition : InnermostTransition program before after)
    (value : Term (signature sig before.1.declarations) Γ .term) (holds : Holds (strategyProgram program) before value)
    {Future : Type} {future : Future → MetaArity sig} (solution : Assignment after.1.declarations future)
    (answer : Term sig Γ .term) (reads : ReadsAt (strategyProgram program) after solution answer) :
    ∃ (old : Assignment before.1.declarations (ground sig)) (call : Term sig Γ .term),
      ReadsAt (strategyProgram program) before old call ∧ Innermost program call answer := by
  obtain ⟨⟨Δ, context, index, bound⟩, valid, rfl⟩ := transition
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
  exact ⟨old, _, readsCall, Δ, context, index, inner, result, rfl, rfl, branch, normal⟩

/-- Every reading after a run of innermost firings is reached by innermost reduction. -/
theorem innermost_runs_backward {call : Term sig Γ .term} {after : State (strategyProgram program)}
    (path : Relation.ReflTransGen (InnermostTransition program) (initial call) after) :
    (∃ value, Holds (strategyProgram program) after value) ∧
      ∀ answer, Reads (strategyProgram program) after answer →
        Relation.ReflTransGen (Innermost program) call answer := by
  induction path with
  | refl =>
      refine ⟨⟨_, initial_holds call⟩, ?_⟩
      rintro answer ⟨Future, future, solution, reads⟩
      obtain rfl := (initial_determines call).2 future solution answer reads
      exact .refl
  | tail _ transition ih =>
      obtain ⟨⟨value, holds⟩, earlier⟩ := ih
      refine ⟨?_, ?_⟩
      · obtain ⟨key, valid, rfl⟩ := transition
        exact ⟨_, (guarded_holds_as_plain _ _ _ valid _).mpr (destination_holds _ _ valid.toPlain holds.1)⟩
      · rintro answer ⟨Future, future, solution, reads⟩
        obtain ⟨old, middle, readsMiddle, step⟩ := innermost_reflected program transition value holds solution answer reads
        exact (earlier middle ⟨_, _, old, readsMiddle⟩).tail step

/-- For determinate equations, every innermost run is a run of innermost firings that fixes its answer. -/
theorem innermost_runs_fixes
    (determinate : ∀ {Δ : Ctx sig} (context : Context Γ Δ) (index : ι), Determinate (raiseAt context (program index)))
    {call answer : Term sig Γ .term} (runs : Relation.ReflTransGen (Innermost program) call answer) :
    ∃ after, Relation.ReflTransGen (InnermostTransition program) (initial call) after ∧
      Fixes (strategyProgram program) after answer := by
  induction runs with
  | refl => exact ⟨initial call, .refl, initial_fixes call⟩
  | tail _ step ih =>
      obtain ⟨middle, path, fixes⟩ := ih
      obtain ⟨Δ, context, index, inner, result, isCall, isAnswer, answered, normal⟩ := step
      obtain ⟨θ, matched, _⟩ := id answered
      subst isCall
      have valid := (innermost_admitted_iff program middle _ fixes.determines ⟨Δ, context, index, termSize inner⟩).mpr
        ⟨inner, rfl, ⟨θ, matched⟩, normal, bounded_size inner⟩
      obtain ⟨next, nextAnswers, nextFixes⟩ := fixes_destination middle _ fixes _ valid.toPlain
        (atContext_determinate grammar context _ (determinate context index))
      have same := Determinate.answer_unique (atContext_determinate grammar context _ (determinate context index))
        nextAnswers ((atContext_answers (grammar := grammar) context _ _ _).mpr ⟨inner, result, rfl, isAnswer, answered⟩)
      subst same
      exact ⟨_, path.tail ⟨⟨Δ, context, index, termSize inner⟩, valid, rfl⟩, nextFixes⟩

/-- **Adequacy of the innermost strategy under binders.** For determinate equations, innermost
reduction in λ contexts reaches exactly the readings of runs of innermost firings. -/
theorem innermost_execution_iff
    (determinate : ∀ {Δ : Ctx sig} (context : Context Γ Δ) (index : ι), Determinate (raiseAt context (program index)))
    (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Innermost program) call answer ↔
      ∃ after, Relation.ReflTransGen (InnermostTransition program) (initial call) after ∧
        Reads (strategyProgram program) after answer := by
  constructor
  · intro runs
    obtain ⟨after, path, fixes⟩ := innermost_runs_fixes program determinate runs
    exact ⟨after, path, fixes.determines.1⟩
  · rintro ⟨after, path, reads⟩
    exact (innermost_runs_backward program path).2 answer reads

#print axioms innermost_reduces
#print axioms plug_source_injective
#print axioms pathEquation_matches_iff
#print axioms pathEquation_pattern
#print axioms mem_carriersOf
#print axioms carriers_absent_at_iff
#print axioms innermost_admitted_iff
#print axioms innermost_step_iff
#print axioms innermost_reflected
#print axioms innermost_runs_backward
#print axioms innermost_runs_fixes
#print axioms innermost_execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Strategy
