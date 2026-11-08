import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersRaising
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersQuoted

/-!
# Raising as a grammar law

A **raising grammar** is a context grammar together with a way to raise a root equation to the
hole of every context, such that raising keeps Miller patterns and every root answer, read through
the context's weakening, is an answer of the raised equation.

- `root_rewrites_everywhere`, `root_runs_everywhere`: a program written at the root rewrites at every
  position of the grammar, with the binders in scope; on the step too (`root_runs_on_step`).
- `raised_principal_first`: raised Miller-pattern programs keep principal answers in every context.
- **Instances:** the λ contexts (`lambdaRaising`, whose raising is R98's `raiseAt`) and the active
  contexts of the quoted-λ account (`quotedRaising`), where `activate` passes no binder.
- **Controls:** under `λx`, the root equation `(= (k $y) $y)` rewrites `(k x)` to `x` in both grammars;
  in the λ grammar, a hole still never captures a binder of the pattern itself
  (`Nested.raised_inner_refused`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern)

/-- **A raising grammar**: root equations raised to every position, with the laws of raising. -/
structure RaisingGrammar (S : Signature) (sort : S.Srt) extends ContextGrammar S sort where
  raise : {Γ Δ : Ctx S} → Context Γ Δ → Equation S Γ sort → Equation S Δ sort
  raise_pattern : ∀ {Γ Δ : Ctx S} (context : Context Γ Δ) (e : Equation S Γ sort),
    Pattern S e.arity e.lhs → Pattern S (raise context e).arity (raise context e).lhs
  raise_answers : ∀ {Γ Δ : Ctx S} (context : Context Γ Δ) (e : Equation S Γ sort) {call answer : Term S Γ sort},
    Answers e call answer →
      Answers (raise context e) (rename (weakening context) call) (rename (weakening context) answer)

variable {S : Signature} {sort : S.Srt} (raising : RaisingGrammar S sort)

/-- A root program, raised to every position. -/
def raisedProgram {Γ : Ctx S} {ι : Type} (program : ι → Equation S Γ sort) : Schema raising.toContextGrammar Γ ι :=
  fun context index => raising.raise context (program index)

variable {raising}

/-- **A root rewrite happens at every position**, read through the position's weakening. -/
theorem root_rewrites_everywhere {Γ : Ctx S} {ι : Type} (program : ι → Equation S Γ sort)
    {call answer : Term S Γ sort} (rewriting : Rewrites program call answer) {Δ : Ctx S}
    (context : raising.Context Γ Δ) :
    CRewrites raising.toContextGrammar (raisedProgram raising program)
      (raising.plugSource context (rename (raising.weakening context) call))
      (raising.plugSource context (rename (raising.weakening context) answer)) := by
  obtain ⟨index, answered⟩ := rewriting
  exact ⟨Δ, context, index, _, _, rfl, rfl, raising.raise_answers context _ answered⟩

/-- **Root runs happen at every position.** -/
theorem root_runs_everywhere {Γ : Ctx S} {ι : Type} (program : ι → Equation S Γ sort)
    {call answer : Term S Γ sort} (runs : Relation.ReflTransGen (Rewrites program) call answer) {Δ : Ctx S}
    (context : raising.Context Γ Δ) :
    Relation.ReflTransGen (CRewrites raising.toContextGrammar (raisedProgram raising program))
      (raising.plugSource context (rename (raising.weakening context) call))
      (raising.plugSource context (rename (raising.weakening context) answer)) := by
  induction runs with
  | refl => exact .refl
  | tail _ rewriting ih => exact ih.tail (root_rewrites_everywhere program rewriting context)

/-- **On the step**: a root run, placed at any position, is read by a run of the contextual step. -/
theorem root_runs_on_step [DecidableEq S.Srt] [ClosedTerms S] {Γ : Ctx S} {ι : Type} [DecidableEq ι]
    (program : ι → Equation S Γ sort) {call answer : Term S Γ sort}
    (runs : Relation.ReflTransGen (Rewrites program) call answer) {Δ : Ctx S} (context : raising.Context Γ Δ) :
    ∃ after, Relation.ReflTransGen (Transition (contextProgram raising.toContextGrammar (raisedProgram raising program)))
        (initial (raising.plugSource context (rename (raising.weakening context) call))) after ∧
      Reads (contextProgram raising.toContextGrammar (raisedProgram raising program)) after
        (raising.plugSource context (rename (raising.weakening context) answer)) :=
  (context_execution_iff _ _ _).mp (root_runs_everywhere program runs context)

/-- **Principal answers in every context.** At the initial state of any call, an admitted firing of a
raised Miller-pattern program, at any position, has a completed worklist run. -/
theorem raised_principal_first [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {Γ : Ctx S} {ι : Type}
    [DecidableEq ι] (program : ι → Equation S Γ sort)
    (patterns : ∀ index, Pattern S (program index).arity (program index).lhs) (call : Term S Γ sort)
    (key : Σ Δ : Ctx S, raising.Context Γ Δ × ι)
    (valid : Admitted (contextProgram raising.toContextGrammar (raisedProgram raising program)) (initial call) key) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem (initial call) key)),
      (letI := (destination (contextProgram raising.toContextGrammar (raisedProgram raising program))
          (initial call) key valid).1.equality;
        ContextualFrameWorklist.run fuel (active (contextProgram raising.toContextGrammar (raisedProgram raising program))
          (initial (program := contextProgram raising.toContextGrammar (raisedProgram raising program)) call).1.declarations)
          (firingProblem (initial call) key)) = .residual update ∧
        update.remaining = [] := by
  obtain ⟨fuel, update, computed, empty, _⟩ := principal_firing (initial call) key valid (initial_pattern call)
    (atContext_pattern key.2.1 _ (raising.raise_pattern key.2.1 (program key.2.2) (patterns key.2.2)))
  exact ⟨fuel, update, computed, empty⟩

/-! ## The λ contexts -/

namespace Nested

open LambdaContextualRung (sig Srt Context appT lamT)

/-- **Raising along a λ context transports root answers** through its weakening. -/
theorem raiseAt_answers {Γ Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Γ .term)
    {call answer : Term sig Γ .term} (answered : Answers e call answer) :
    Answers (raiseAt context e) (rename (weakening context) call) (rename (weakening context) answer) := by
  induction context with
  | hole =>
      change Answers e (rename (fun _ position => position) call) (rename (fun _ position => position) answer)
      rw [rename_id, rename_id]
      exact answered
  | appLeft inner _ ih => exact ih e answered
  | appRight _ inner ih => exact ih e answered
  | underLam inner ih =>
      have raised := ih (raiseOne Srt.term e) (raise_answers Srt.term e answered)
      rw [weaken, weaken, rename_comp, rename_comp] at raised
      exact raised

/-- The λ contexts are a raising grammar, by R98's `raiseAt`. -/
def lambdaRaising : RaisingGrammar sig .term :=
  { grammar with
    raise := raiseAt
    raise_pattern := raiseAt_pattern
    raise_answers := raiseAt_answers }

theorem lambda_raised_is_raisedSchema {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term)
    {Δ : Ctx sig} (context : Context Γ Δ) (index : ι) :
    raisedProgram lambdaRaising program context index = raisedSchema program context index := rfl

/-- **Control**: the root `(= (k $y) $y)` at `(k g)`, placed under `λx`, rewrites by the law. -/
theorem lambda_law_under_binder :
    CRewrites grammar (raisedSchema fun _ : Unit => callRoot)
      (lamT (appT (.var (.succ .zero)) (.var (.succ (.succ .zero)))) : Term sig Controls.Consts .term)
      (lamT (.var (.succ (.succ .zero)))) := by
  have root : Rewrites (fun _ : Unit => callRoot) (appT Controls.fC Controls.gC) Controls.gC :=
    ⟨(), fun _ => Controls.gC, rfl, rfl⟩
  exact root_rewrites_everywhere (raising := lambdaRaising) _ root (Context.underLam .hole)

end Nested

/-! ## The active contexts of the quoted-λ account -/

namespace Quoted

open QuotedLambda (sig Context)
open LambdaContextualRung (Srt)

/-- Raise along the binders an active context passes: `λ` passes one, `activate` none. -/
def raiseAt : {Γ Δ : Ctx sig} → Context Γ Δ → Equation sig Γ .term → Equation sig Δ .term
  | _, _, .hole, e => e
  | _, _, .appLeft inner _, e => raiseAt inner e
  | _, _, .appRight _ inner, e => raiseAt inner e
  | _, _, .underLam inner, e => raiseAt inner (raiseOne Srt.term e)
  | _, _, .underActivate inner, e => raiseAt inner e

theorem raiseAt_pattern {Γ Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Γ .term)
    (patterned : Pattern sig e.arity e.lhs) : Pattern sig (raiseAt context e).arity (raiseAt context e).lhs := by
  induction context with
  | hole => exact patterned
  | appLeft inner _ ih => exact ih e patterned
  | appRight _ inner ih => exact ih e patterned
  | underLam inner ih => exact ih _ (raiseOne_pattern Srt.term e patterned)
  | underActivate inner ih => exact ih e patterned

theorem raiseAt_answers {Γ Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Γ .term)
    {call answer : Term sig Γ .term} (answered : Answers e call answer) :
    Answers (raiseAt context e) (rename (weakening context) call) (rename (weakening context) answer) := by
  induction context with
  | hole =>
      change Answers e (rename (fun _ position => position) call) (rename (fun _ position => position) answer)
      rw [rename_id, rename_id]
      exact answered
  | appLeft inner _ ih => exact ih e answered
  | appRight _ inner ih => exact ih e answered
  | underLam inner ih =>
      have raised := ih (raiseOne Srt.term e) (raise_answers Srt.term e answered)
      rw [weaken, weaken, rename_comp, rename_comp] at raised
      exact raised
  | underActivate inner ih => exact ih e answered

/-- The active contexts of the quoted-λ account are a raising grammar. -/
def quotedRaising : RaisingGrammar sig .term :=
  { grammar with
    raise := raiseAt
    raise_pattern := raiseAt_pattern
    raise_answers := raiseAt_answers }

/-- One constant `k`. -/
abbrev QConsts : Ctx sig := [.term]

/-- `(= (k $y) $y)` in the quoted signature. -/
def kRoot : Equation sig QConsts .term :=
  ⟨Unit, inferInstance, fun _ => (QConsts, .term), QuotedLambdaExecution.app _ (.var .zero) (generator _ ()),
    generator _ ()⟩

/-- **Control**: raised under `λx`, the hole of `(= (k $y) $y)` may take `x`: `λx. (k x)` rewrites to
`λx. x`. -/
theorem quoted_raised_under_binder :
    CRewrites grammar (raisedProgram quotedRaising fun _ : Unit => kRoot)
      (QuotedLambda.lam (QuotedLambda.app (.var (.succ .zero)) (.var .zero)) : Term sig QConsts .term)
      (QuotedLambda.lam (.var .zero)) :=
  ⟨_, .underLam .hole, (), _, _, rfl, rfl, fun _ => .var .zero, rfl, rfl⟩

/-- **Control**: under `activate`, no binder is passed; the root answer is read unchanged. -/
theorem quoted_law_under_activate :
    CRewrites grammar (raisedProgram quotedRaising fun _ : Unit => kRoot)
      (QuotedLambda.activate (QuotedLambda.app (.var .zero) (.var .zero)) : Term sig QConsts .term)
      (QuotedLambda.activate (.var .zero)) := by
  have root : Rewrites (fun _ : Unit => kRoot) (QuotedLambda.app (.var .zero) (.var .zero)) (.var .zero) :=
    ⟨(), fun _ => .var .zero, rfl, rfl⟩
  exact root_rewrites_everywhere (raising := quotedRaising) _ root (Context.underActivate .hole)

end Quoted

#print axioms root_rewrites_everywhere
#print axioms root_runs_everywhere
#print axioms root_runs_on_step
#print axioms raised_principal_first
#print axioms Nested.raiseAt_answers
#print axioms Nested.lambda_law_under_binder
#print axioms Quoted.raiseAt_pattern
#print axioms Quoted.raiseAt_answers
#print axioms Quoted.quoted_raised_under_binder
#print axioms Quoted.quoted_law_under_activate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
