-- LLM primer: Formalizes the binding consistency invariant for CeTTa's
-- typed-apply machine. Bindings accumulated through evaluation must be
-- loop-free. Connects to TypedApplyDirect's mergeEnv/extendBinder parameters.

import Mettapedia.Languages.MeTTa.HE.TypedApplyMachine

/-!
# Binding Consistency Invariant

Formalizes that bindings accumulated during typed ordinary application
remain consistent (loop-free) at every step.

## Why This Matters

CeTTa's `mergeBindings` and `bind_domain_binder_builder` can produce
bindings with variable loops (`$x → $y, $y → $x`). The evaluator checks
`hasLoop` and discards looping bindings (EvalSpec.MettaCall.equation_match
requires `h_no_loop : merged.hasLoop = false`). If this check is missed,
evaluation produces garbage.

For the ATP seam: unification must produce consistent substitutions.
The same invariant ensures unification results are well-formed.

For TransWeave: search state validity requires consistent bindings
at every MDP state. Looping bindings would make the value function
undefined.

## Design

A `ConsistentMerge` predicate on the `mergeEnv` parameter: if the input
bindings are loop-free and merge succeeds, the output is also loop-free.

A `ConsistentExtend` predicate on `extendBinder`: if input is loop-free
and extension succeeds, output is loop-free.

Then: the typed-apply machine preserves loop-freedom through all steps,
given `ConsistentMerge` and `ConsistentExtend`.

## C Seam Mapping

| Lean | C (eval.c) |
|------|-----------|
| `Bindings.hasLoop = false` | `!bindings_has_loop(merged)` in mergeBindings |
| `ConsistentMerge` | `bindings_builder_merge_or_clone` only succeeds with consistent result |
| `ConsistentExtend` | `bind_domain_binder_builder` preserves consistency |
| `BindingsSafe` | loop-freedom of env in every machine state |
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Consistency Predicates -/

/-- A merge function is consistent if: when both inputs are loop-free and
    merge succeeds, the output is also loop-free. -/
def ConsistentMerge (mergeEnv : Bindings → Bindings → Option Bindings) : Prop :=
  ∀ b1 b2 merged,
    b1.hasLoop = false →
    mergeEnv b1 b2 = some merged →
    merged.hasLoop = false

/-- A binder extension function is consistent if: when the input is
    loop-free and extension succeeds, the output is also loop-free. -/
def ConsistentExtend (extendBinder : Bindings → Atom → Atom → Option Bindings) : Prop :=
  ∀ b argType argVal extended,
    b.hasLoop = false →
    extendBinder b argType argVal = some extended →
    extended.hasLoop = false

/-! ## Machine Binding Safety -/

/-- The binding safety invariant for a typed-apply state: the accumulated
    environment is loop-free. -/
def StateSafe (st : TypedApplyState) : Prop :=
  st.env.hasLoop = false

/-- The binding safety invariant for a machine config: every frame's
    state has loop-free bindings. -/
def BindingsSafe (cfg : TypedApplyConfig) : Prop :=
  ∀ f, f ∈ cfg.worklist → match f with
    | TypedApplyFrame.apply st => st.env.hasLoop = false
    | TypedApplyFrame.argConsumer _ _ _ st => st.env.hasLoop = false

/-! ## Preservation -/

theorem bindingsSafe_initial (st : TypedApplyState) (h : st.env.hasLoop = false) :
    BindingsSafe (TypedApplyConfig.initial st) := by
  intro f hf; simp [TypedApplyConfig.initial] at hf; subst hf; exact h

/-- Binding safety is preserved by every machine step, given consistent
    merge and extend functions.

    Key: each step that creates a new frame derives its env from either
    (a) the parent env directly (fast path), or
    (b) a successful merge + extend (eval path).
    Both (a) and (b) preserve loop-freedom under the consistency hypotheses. -/
theorem bindingsSafe_step
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (h_merge : ConsistentMerge mergeEnv)
    (h_extend : ConsistentExtend extendBinder)
    (cfg cfg' : TypedApplyConfig)
    (hSafe : BindingsSafe cfg)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    BindingsSafe cfg' := by
  intro f hf
  cases hStep with
  | applyComplete st rest emitted _ =>
    exact hSafe f (by simp [hf])
  | applyTrivialOk st rest emitted boundArg argType env' h_lt h_triv h_bound h_type h_ext =>
    simp at hf; rcases hf with rfl | hf
    · -- New apply frame with env' = extendBinder st.env ...
      have h_st := hSafe (TypedApplyFrame.apply st) (by simp)
      simp at h_st
      exact h_extend st.env argType boundArg env' h_st h_ext
    · exact hSafe f (by simp [hf])
  | applyTrivialFail _ _ _ _ _ _ _ _ _ _ =>
    exact hSafe f (by simp [hf])
  | applyEval st rest emitted _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · -- ArgConsumer frame inherits st's env (unchanged)
      exact hSafe (TypedApplyFrame.apply st) (by simp)
    · exact hSafe f (by simp [hf])
  | consumeMergeFail argVal evalEnv pending origArg argType st rest emitted _ =>
    simp at hf; rcases hf with rfl | hf
    · exact hSafe (TypedApplyFrame.argConsumer ((argVal, evalEnv) :: pending) origArg argType st) (by simp)
    · exact hSafe f (by simp [hf])
  | consumeError argVal evalEnv pending origArg argType st rest emitted mergedEnv h_mg _ _ =>
    simp at hf; rcases hf with rfl | hf
    · exact hSafe (TypedApplyFrame.argConsumer ((argVal, evalEnv) :: pending) origArg argType st) (by simp)
    · exact hSafe f (by simp [hf])
  | consumeBinderFail argVal evalEnv pending origArg argType st rest emitted _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · exact hSafe (TypedApplyFrame.argConsumer ((argVal, evalEnv) :: pending) origArg argType st) (by simp)
    · exact hSafe f (by simp [hf])
  | consumeOk argVal evalEnv pending origArg argType st rest emitted mergedEnv extEnv h_mg h_ok h_ext =>
    simp at hf; rcases hf with rfl | hf
    · -- New apply frame with extEnv = extendBinder mergedEnv ...
      -- mergedEnv came from mergeEnv st.env evalEnv
      -- st.env is loop-free (by hSafe on the parent argConsumer)
      have h_parent := hSafe (TypedApplyFrame.argConsumer ((argVal, evalEnv) :: pending) origArg argType st) (by simp)
      simp at h_parent
      have h_merged := h_merge st.env evalEnv mergedEnv h_parent h_mg
      exact h_extend mergedEnv argType argVal extEnv h_merged h_ext
    · rcases hf with rfl | hf
      · exact hSafe (TypedApplyFrame.argConsumer ((argVal, evalEnv) :: pending) origArg argType st) (by simp)
      · exact hSafe f (by simp [hf])
  | consumeExhausted _ _ _ _ _ =>
    exact hSafe f (by simp [hf])

/-- Binding safety preserved across reachability. -/
theorem bindingsSafe_reaches
    (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (h_merge : ConsistentMerge mergeEnv)
    (h_extend : ConsistentExtend extendBinder)
    (cfg cfg' : TypedApplyConfig)
    (hSafe : BindingsSafe cfg)
    (hReach : TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    BindingsSafe cfg' := by
  induction hReach with
  | refl => exact hSafe
  | step hs _ ih => exact ih (bindingsSafe_step _ _ _ _ _ h_merge h_extend _ _ hSafe hs)

/-! ## Concrete Instances -/

-- Note: (fun _ b => some b) is NOT a ConsistentMerge — b2 could have loops.
-- The real C merge (bindings_builder_merge_or_clone) checks consistency.

/-- A merge that returns the FIRST argument is trivially consistent. -/
theorem consistentMerge_fst : ConsistentMerge (fun b _ => some b) := by
  intro b1 _ merged h1 h_merge
  simp at h_merge; subst h_merge; exact h1

/-- An extend that returns the input unchanged is consistent. -/
theorem consistentExtend_id : ConsistentExtend (fun b _ _ => some b) := by
  intro b _ _ extended h h_ext
  simp at h_ext; subst h_ext; exact h

end Mettapedia.Languages.MeTTa.HE
