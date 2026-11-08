import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPrincipal

/-!
# Equations in evaluation contexts, under binders

A **context grammar** fixes the positions where a call may be rewritten: one-hole contexts, which
may pass under binders, with their plugging on source terms and on terms with holes. Each context
also weakens the outer context into the hole's context, so constants keep their identity under
binders.

A program in contexts is a **schema**: for every context, equations at the hole's context. Their
holes may list the binders in scope at the call, and their constants are read through the
context's weakening. An equation written at the root is raised along the context's binders
(`ProgramBindersRaising`).

**The reference semantics** (`CRewrites`): a call is a plugged term `C[t]`, and `t` rewrites by the
schema at the hole's context. It is defined from the source plugging only.

**The translation:** an equation at a context is itself an equation at the root, the plugged
equation `(= C[lhs] C[rhs])` (`atContext`). So the program in contexts is a root program, and its
firings are those of the binder-bearing core.
- `atContext_answers`: the plugged equation answers exactly the plugged answers of the equation.
- `context_rewrites_iff`, `context_execution_iff`: runs of the reference semantics are exactly the
  readings of runs of the contextual step.
- `context_principal_firing`: plugging keeps Miller patterns, so the worklist computes principal
  answers as at the root.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern)

/-- One-hole contexts of a signature at a sort, with the laws of plugging. -/
structure ContextGrammar (S : Signature) (sort : S.Srt) where
  Context : Ctx S → Ctx S → Type
  contextEq : ∀ Γ Δ, DecidableEq (Context Γ Δ)
  /-- The outer context, weakened into the hole's context. -/
  weakening : {Γ Δ : Ctx S} → Context Γ Δ → Ren S Γ Δ
  plugSource : {Γ Δ : Ctx S} → Context Γ Δ → Term S Δ sort → Term S Γ sort
  plug : {W : Type} → (declaration : W → MetaArity S) → {Γ Δ : Ctx S} → Context Γ Δ →
    Term (signature S declaration) Δ sort → Term (signature S declaration) Γ sort
  plug_include : ∀ {W : Type} (declaration : W → MetaArity S) {Γ Δ : Ctx S} (context : Context Γ Δ)
    (term : Term S Δ sort),
      plug declaration context (Rigid.includeTerm declaration term) =
        Rigid.includeTerm declaration (plugSource context term)
  instantiate_plug : ∀ {W X : Type} {declaration : W → MetaArity S} {next : X → MetaArity S}
    (change : Assignment declaration next) {Γ Δ : Ctx S} (context : Context Γ Δ)
    (term : Term (signature S declaration) Δ sort),
      instantiate change (plug declaration context term) = plug next context (instantiate change term)
  plug_injective : ∀ {W : Type} (declaration : W → MetaArity S) {Γ Δ : Ctx S} (context : Context Γ Δ),
    Function.Injective (plug declaration context)
  plug_pattern : ∀ {W : Type} {declaration : W → MetaArity S} {Γ Δ : Ctx S} (context : Context Γ Δ)
    (term : Term (signature S declaration) Δ sort),
      Pattern S declaration term → Pattern S declaration (plug declaration context term)
  plug_recovers : ∀ {W : Type} {declaration : W → MetaArity S} {Γ Δ : Ctx S} (context : Context Γ Δ)
    (value : Term (signature S declaration) Δ sort) (term : Term S Γ sort),
      plug declaration context value = Rigid.includeTerm declaration term →
        ∃ inner, term = plugSource context inner ∧ value = Rigid.includeTerm declaration inner

variable {S : Signature} {sort : S.Srt} (grammar : ContextGrammar S sort)

instance (Γ Δ : Ctx S) : DecidableEq (grammar.Context Γ Δ) := grammar.contextEq Γ Δ

/-- An equation at the hole's context, as an equation at the root. -/
def atContext {Γ Δ : Ctx S} (context : grammar.Context Γ Δ) (e : Equation S Δ sort) : Equation S Γ sort :=
  ⟨e.Holes, e.holesEq, e.arity, grammar.plug e.arity context e.lhs, grammar.plug e.arity context e.rhs⟩

variable {grammar}

theorem atContext_reads {Γ Δ : Ctx S} (context : grammar.Context Γ Δ) (e : Equation S Δ sort) (θ : e.Ground)
    (term : Term (signature S e.arity) Δ sort) (value : Term S Γ sort) :
    instantiate (e.assign θ (ground S)) (grammar.plug e.arity context term) = Rigid.includeTerm (ground S) value ↔
      ∃ inner, value = grammar.plugSource context inner ∧
        instantiate (e.assign θ (ground S)) term = Rigid.includeTerm (ground S) inner := by
  rw [grammar.instantiate_plug]
  constructor
  · exact grammar.plug_recovers context _ value
  · rintro ⟨inner, rfl, read⟩
    rw [read, grammar.plug_include]

/-- **The plugged equation answers exactly the plugged answers.** -/
theorem atContext_answers {Γ Δ : Ctx S} (context : grammar.Context Γ Δ) (e : Equation S Δ sort)
    (call answer : Term S Γ sort) :
    Answers (atContext grammar context e) call answer ↔
      ∃ inner result, call = grammar.plugSource context inner ∧ answer = grammar.plugSource context result ∧
        Answers e inner result := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    obtain ⟨inner, rfl, readCall⟩ := (atContext_reads context e θ e.lhs call).mp matched
    obtain ⟨result, rfl, readAnswer⟩ := (atContext_reads context e θ e.rhs answer).mp answered
    exact ⟨inner, result, rfl, rfl, θ, readCall, readAnswer⟩
  · rintro ⟨inner, result, rfl, rfl, θ, matched, answered⟩
    exact ⟨θ, (atContext_reads context e θ e.lhs _).mpr ⟨inner, rfl, matched⟩,
      (atContext_reads context e θ e.rhs _).mpr ⟨result, rfl, answered⟩⟩

theorem atContext_pattern {Γ Δ : Ctx S} (context : grammar.Context Γ Δ) (e : Equation S Δ sort)
    (patterned : Pattern S e.arity e.lhs) :
    Pattern S (atContext grammar context e).arity (atContext grammar context e).lhs :=
  grammar.plug_pattern context e.lhs patterned

variable (grammar) in
/-- A program in contexts: for every context of the root context `Γ`, equations at the hole's
context. A schema may read the context's weakening, or raise a root equation along its binders. -/
abbrev Schema (Γ : Ctx S) (ι : Type) :=
  {Δ : Ctx S} → grammar.Context Γ Δ → ι → Equation S Δ sort

variable (grammar) {ι : Type} {Γ : Ctx S}

/-- **The reference semantics in contexts.** The call is `C[t]`, and `t` rewrites by the schema at
the hole's context. -/
def CRewrites (schema : Schema grammar Γ ι) (call answer : Term S Γ sort) : Prop :=
  ∃ (Δ : Ctx S) (context : grammar.Context Γ Δ) (index : ι) (inner result : Term S Δ sort),
    call = grammar.plugSource context inner ∧ answer = grammar.plugSource context result ∧
      Answers (schema context index) inner result

/-- The program in contexts as a root program: one plugged equation per context and equation. -/
def contextProgram (schema : Schema grammar Γ ι) : (Σ Δ : Ctx S, grammar.Context Γ Δ × ι) → Equation S Γ sort :=
  fun key => atContext grammar key.2.1 (schema key.2.1 key.2.2)

variable {grammar}

theorem context_rewrites_iff (schema : Schema grammar Γ ι) (call answer : Term S Γ sort) :
    Rewrites (contextProgram grammar schema) call answer ↔ CRewrites grammar schema call answer := by
  constructor
  · rintro ⟨⟨Δ, context, index⟩, answered⟩
    obtain ⟨inner, result, rfl, rfl, branch⟩ := (atContext_answers context _ call answer).mp answered
    exact ⟨Δ, context, index, inner, result, rfl, rfl, branch⟩
  · rintro ⟨Δ, context, index, inner, result, rfl, rfl, branch⟩
    exact ⟨⟨Δ, context, index⟩, (atContext_answers context _ _ _).mpr ⟨inner, result, rfl, rfl, branch⟩⟩

theorem context_runs_iff (schema : Schema grammar Γ ι) (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites (contextProgram grammar schema)) call answer ↔
      Relation.ReflTransGen (CRewrites grammar schema) call answer := by
  have same : Rewrites (contextProgram grammar schema) = CRewrites grammar schema := by
    funext first second
    exact propext (context_rewrites_iff schema first second)
  rw [same]

variable [DecidableEq S.Srt] [DecidableEq ι] [ClosedTerms S]

/-- **Adequacy in contexts.** Runs of the reference semantics in contexts reach exactly the readings
of the runs of the contextual step from the initial state of the call. -/
theorem context_execution_iff (schema : Schema grammar Γ ι) (call answer : Term S Γ sort) :
    Relation.ReflTransGen (CRewrites grammar schema) call answer ↔
      ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar schema)) (initial call) after ∧
        Reads (contextProgram grammar schema) after answer :=
  (context_runs_iff schema call answer).symm.trans (execution_iff call answer)

variable [∀ result, DecidableEq (S.Op result)]

omit [ClosedTerms S] in
/-- **Principal answers in contexts.** At a state in the pattern fragment, an admitted firing of a
plugged Miller-pattern equation has a completed worklist run, and its result reads exactly as the
instances of the computed answer. -/
theorem context_principal_firing (schema : Schema grammar Γ ι)
    (state : State (contextProgram grammar schema)) (key : Σ Δ : Ctx S, grammar.Context Γ Δ × ι)
    (valid : Admitted (contextProgram grammar schema) state key) (patterned : PatternState state)
    (lhsPattern : Pattern S (schema key.2.1 key.2.2).arity (schema key.2.1 key.2.2).lhs) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem state key)),
      (letI := (destination (contextProgram grammar schema) state key valid).1.equality;
        ContextualFrameWorklist.run fuel (active (contextProgram grammar schema) state.1.declarations)
          (firingProblem state key)) = .residual update ∧
        update.remaining = [] ∧
        ∀ answer, Reads (contextProgram grammar schema) (destination (contextProgram grammar schema) state key valid)
            answer ↔
          ∃ (Future : Type) (future : Future → MetaArity S) (factor : Assignment update.declaration future),
            instantiate factor (instantiate update.answer
              (output (contextProgram grammar schema) state.1.declarations key state.1.occupied state.2)) =
                Rigid.includeTerm future answer :=
  principal_firing state key valid patterned (atContext_pattern key.2.1 _ lhsPattern)

#print axioms atContext_answers
#print axioms atContext_pattern
#print axioms context_rewrites_iff
#print axioms context_runs_iff
#print axioms context_execution_iff
#print axioms context_principal_firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
