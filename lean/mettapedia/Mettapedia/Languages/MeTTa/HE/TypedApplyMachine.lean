-- LLM primer: Models ALL failure modes from C: merge failure, binder failure.
-- Step relation has 10 constructors. processFrame split into per-frame helpers
-- to avoid cross-branch unfold issues in proofs.

import Mettapedia.Languages.MeTTa.HE.TypedApplyDirect
import Mettapedia.Languages.MeTTa.HE.OwnershipInvariant

/-!
# Explicit-Stack Typed Ordinary Application Machine

Matches `TypedApplyDirect.typedApplyDirect` exactly, including failure modes.

## Key Results

- `PrefixInvariant` preservation
- `processFrame_spec` — frame processing realizes the step relation
- `stepConfig_spec` — executable step realizes inductive step
- `machineRun_reaches` — fuel runner induces reachability
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive TypedApplyFrame where
  | apply (st : TypedApplyState)
  | argConsumer (pending : ResultList) (origArg : Atom) (argType : Atom) (st : TypedApplyState)
  deriving Repr

structure TypedApplyConfig where
  worklist : List TypedApplyFrame
  emitted  : ResultList
  deriving Repr

def TypedApplyState.advance (st : TypedApplyState) (argVal : Atom) (env' : Bindings) :
    TypedApplyState :=
  ⟨st.headAtom, st.origArgs, st.argTypes, st.idx + 1, st.evArgs ++ [argVal], env'⟩

/-! ## Step Relation -/

inductive TypedApplyStep
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) :
    TypedApplyConfig → TypedApplyConfig → Prop where
  | applyComplete (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (h : st.idx ≥ st.origArgs.length) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.apply st :: rest, emitted⟩
        ⟨rest, emitted ++ [(.expression (st.headAtom :: st.evArgs), st.env)]⟩
  | applyTrivialOk (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (boundArg argType : Atom) (env' : Bindings)
      (h_lt : st.idx < st.origArgs.length)
      (h_trivial : isTrivial argType = true ∨ st.origArgs[st.idx].isVariable = true)
      (h_bound : boundArg = applyEnv st.env st.origArgs[st.idx])
      (h_type : argType = if h' : st.idx < st.argTypes.length then st.argTypes[st.idx] else Atom.undefinedType)
      (h_ext : extendBinder st.env argType boundArg = some env') :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.apply st :: rest, emitted⟩ ⟨.apply (st.advance boundArg env') :: rest, emitted⟩
  | applyTrivialFail (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (boundArg argType : Atom)
      (h_lt : st.idx < st.origArgs.length)
      (h_trivial : isTrivial argType = true ∨ st.origArgs[st.idx].isVariable = true)
      (h_bound : boundArg = applyEnv st.env st.origArgs[st.idx])
      (h_type : argType = if h' : st.idx < st.argTypes.length then st.argTypes[st.idx] else Atom.undefinedType)
      (h_ext : extendBinder st.env argType boundArg = none) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.apply st :: rest, emitted⟩ ⟨rest, emitted⟩
  | applyEval (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (origArg argType boundArg : Atom) (results : ResultList)
      (h_lt : st.idx < st.origArgs.length)
      (h_not_trivial : ¬(isTrivial argType = true ∨ origArg.isVariable = true))
      (h_orig : origArg = st.origArgs[st.idx])
      (h_type : argType = if h' : st.idx < st.argTypes.length then st.argTypes[st.idx] else Atom.undefinedType)
      (h_bound : boundArg = applyEnv st.env origArg)
      (h_results : results = eval1 boundArg argType st.env) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.apply st :: rest, emitted⟩
        ⟨.argConsumer results origArg argType st :: rest, emitted⟩
  | consumeMergeFail (argVal : Atom) (evalEnv : Bindings) (pending : ResultList)
      (origArg argType : Atom) (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (h_merge : mergeEnv st.env evalEnv = none) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.argConsumer ((argVal, evalEnv) :: pending) origArg argType st :: rest, emitted⟩
        ⟨.argConsumer pending origArg argType st :: rest, emitted⟩
  | consumeError (argVal : Atom) (evalEnv : Bindings) (pending : ResultList)
      (origArg argType : Atom) (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (mergedEnv : Bindings)
      (h_merge : mergeEnv st.env evalEnv = some mergedEnv)
      (h_err : isEmptyOrError argVal = true) (h_changed : argVal ≠ origArg) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.argConsumer ((argVal, evalEnv) :: pending) origArg argType st :: rest, emitted⟩
        ⟨.argConsumer pending origArg argType st :: rest, emitted ++ [(argVal, mergedEnv)]⟩
  | consumeBinderFail (argVal : Atom) (evalEnv : Bindings) (pending : ResultList)
      (origArg argType : Atom) (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (mergedEnv : Bindings)
      (h_merge : mergeEnv st.env evalEnv = some mergedEnv)
      (h_ok : isEmptyOrError argVal = false ∨ argVal = origArg)
      (h_ext : extendBinder mergedEnv argType argVal = none) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.argConsumer ((argVal, evalEnv) :: pending) origArg argType st :: rest, emitted⟩
        ⟨.argConsumer pending origArg argType st :: rest, emitted⟩
  | consumeOk (argVal : Atom) (evalEnv : Bindings) (pending : ResultList)
      (origArg argType : Atom) (st : TypedApplyState) (rest : List TypedApplyFrame)
      (emitted : ResultList) (mergedEnv extEnv : Bindings)
      (h_merge : mergeEnv st.env evalEnv = some mergedEnv)
      (h_ok : isEmptyOrError argVal = false ∨ argVal = origArg)
      (h_ext : extendBinder mergedEnv argType argVal = some extEnv) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.argConsumer ((argVal, evalEnv) :: pending) origArg argType st :: rest, emitted⟩
        ⟨.apply (st.advance argVal extEnv) :: .argConsumer pending origArg argType st :: rest, emitted⟩
  | consumeExhausted (origArg argType : Atom) (st : TypedApplyState)
      (rest : List TypedApplyFrame) (emitted : ResultList) :
      TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
        ⟨.argConsumer [] origArg argType st :: rest, emitted⟩ ⟨rest, emitted⟩

/-! ## Reachability -/

inductive TypedApplyReaches (eval1 applyEnv mergeEnv extendBinder isTrivial) :
    TypedApplyConfig → TypedApplyConfig → Prop where
  | refl : TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg
  | step : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg₁ cfg₂ →
           TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg₂ cfg₃ →
           TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg₁ cfg₃

/-! ## Invariants -/

def PrefixInvariant (cfg : TypedApplyConfig) : Prop :=
  ∀ f, f ∈ cfg.worklist → match f with
    | .apply st => st.evArgs.length = st.idx
    | .argConsumer _ _ _ st => st.evArgs.length = st.idx

def TypedApplyConfig.initial (st : TypedApplyState) : TypedApplyConfig := ⟨[.apply st], []⟩

theorem prefixInvariant_initial (st : TypedApplyState) (h : st.evArgs.length = st.idx) :
    PrefixInvariant (.initial st) := by
  intro f hf; simp [TypedApplyConfig.initial] at hf; subst hf; exact h

/-! ## Per-Frame Helpers (split to avoid cross-branch unfold) -/

/-- Compute the argument type at position idx, defaulting to %Undefined%. -/
def getArgType (st : TypedApplyState) : Atom :=
  if h' : st.idx < st.argTypes.length then st.argTypes[st.idx] else Atom.undefinedType

def processApplyFrame (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (st : TypedApplyState) (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyConfig :=
  if h : st.idx ≥ st.origArgs.length then
    ⟨rest, emitted ++ [(.expression (st.headAtom :: st.evArgs), st.env)]⟩
  else
    have h_lt : st.idx < st.origArgs.length := Nat.lt_of_not_le h
    let origArg := st.origArgs[st.idx]
    let argType := getArgType st
    let boundArg := applyEnv st.env origArg
    if isTrivial argType || origArg.isVariable then
      match extendBinder st.env argType boundArg with
      | none => ⟨rest, emitted⟩
      | some env' => ⟨.apply (st.advance boundArg env') :: rest, emitted⟩
    else ⟨.argConsumer (eval1 boundArg argType st.env) origArg argType st :: rest, emitted⟩

/-- Process an ArgConsumer frame. -/
def processConsumerFrame (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (pending : ResultList) (origArg argType : Atom) (st : TypedApplyState)
    (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyConfig :=
  match pending with
  | [] => ⟨rest, emitted⟩
  | (argVal, evalEnv) :: pending' =>
    match mergeEnv st.env evalEnv with
    | none => ⟨.argConsumer pending' origArg argType st :: rest, emitted⟩
    | some mergedEnv =>
      if isEmptyOrError argVal && decide (argVal ≠ origArg) then
        ⟨.argConsumer pending' origArg argType st :: rest, emitted ++ [(argVal, mergedEnv)]⟩
      else match extendBinder mergedEnv argType argVal with
           | none => ⟨.argConsumer pending' origArg argType st :: rest, emitted⟩
           | some extEnv =>
             ⟨.apply (st.advance argVal extEnv) :: .argConsumer pending' origArg argType st :: rest, emitted⟩

/-- processFrame dispatches to per-frame helpers. -/
def processFrame (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (frame : TypedApplyFrame) (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyConfig :=
  match frame with
  | .apply st => processApplyFrame eval1 applyEnv extendBinder isTrivial st rest emitted
  | .argConsumer pending origArg argType st =>
    processConsumerFrame mergeEnv extendBinder pending origArg argType st rest emitted

/-! ## Bridge Theorems -/

theorem processApplyFrame_spec (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
      ⟨.apply st :: rest, emitted⟩
      (processApplyFrame eval1 applyEnv extendBinder isTrivial st rest emitted) := by
  unfold processApplyFrame getArgType
  by_cases h_ge : st.idx ≥ st.origArgs.length
  · simp [h_ge]; exact .applyComplete st rest emitted h_ge
  · have h_lt : st.idx < st.origArgs.length := by omega
    simp [h_ge]
    by_cases h_types : st.idx < st.argTypes.length
    · -- argType = st.argTypes[st.idx]
      simp [dif_pos h_types]
      by_cases h_triv : (isTrivial st.argTypes[st.idx] || st.origArgs[st.idx].isVariable) = true
      · have h_prop : isTrivial st.argTypes[st.idx] = true ∨ st.origArgs[st.idx].isVariable = true :=
          by rcases Bool.or_eq_true_iff.mp h_triv with h | h <;> [exact Or.inl h; exact Or.inr h]
        simp [if_pos h_prop]
        cases h_ext : extendBinder st.env st.argTypes[st.idx] (applyEnv st.env st.origArgs[st.idx]) with
        | none =>
          exact .applyTrivialFail st rest emitted _ _ h_lt h_prop rfl ((dif_pos h_types).symm) h_ext
        | some env' =>
          exact .applyTrivialOk st rest emitted _ _ env' h_lt h_prop rfl ((dif_pos h_types).symm) h_ext
      · have h_prop : ¬(isTrivial st.argTypes[st.idx] = true ∨ st.origArgs[st.idx].isVariable = true) := by
          intro h_or; rcases h_or with h | h
          · exact absurd (show (_ || _) = true by simp [h]) h_triv
          · exact absurd (show (_ || _) = true by simp [h]) h_triv
        simp [if_neg h_prop]
        exact .applyEval st rest emitted _ _ _ _ h_lt h_prop rfl ((dif_pos h_types).symm) rfl rfl
    · -- argType = Atom.undefinedType
      simp [dif_neg h_types]
      by_cases h_triv : (isTrivial Atom.undefinedType || st.origArgs[st.idx].isVariable) = true
      · have h_prop : isTrivial Atom.undefinedType = true ∨ st.origArgs[st.idx].isVariable = true :=
          by rcases Bool.or_eq_true_iff.mp h_triv with h | h <;> [exact Or.inl h; exact Or.inr h]
        simp [if_pos h_prop]
        cases h_ext : extendBinder st.env Atom.undefinedType (applyEnv st.env st.origArgs[st.idx]) with
        | none =>
          exact .applyTrivialFail st rest emitted _ _ h_lt h_prop rfl (by simp [dif_neg h_types]) h_ext
        | some env' =>
          exact .applyTrivialOk st rest emitted _ _ env' h_lt h_prop rfl (by simp [dif_neg h_types]) h_ext
      · have h_prop : ¬(isTrivial Atom.undefinedType = true ∨ st.origArgs[st.idx].isVariable = true) := by
          intro h_or; rcases h_or with h | h
          · exact absurd (show (_ || _) = true by simp [h]) h_triv
          · exact absurd (show (_ || _) = true by simp [h]) h_triv
        simp [if_neg h_prop]
        exact .applyEval st rest emitted _ _ _ _ h_lt h_prop rfl (by simp [h_types]) rfl rfl

theorem processConsumerFrame_spec (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (pending : ResultList) (origArg argType : Atom) (st : TypedApplyState)
    (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
      ⟨.argConsumer pending origArg argType st :: rest, emitted⟩
      (processConsumerFrame mergeEnv extendBinder pending origArg argType st rest emitted) := by
  cases pending with
  | nil => exact .consumeExhausted origArg argType st rest emitted
  | cons r pending' =>
    obtain ⟨argVal, evalEnv⟩ := r
    simp only [processConsumerFrame]
    split
    · next h_merge => exact .consumeMergeFail argVal evalEnv pending' origArg argType st rest emitted h_merge
    · next mergedEnv h_merge =>
      split
      · next h_err =>
        simp at h_err; obtain ⟨h1, h2⟩ := h_err
        exact .consumeError argVal evalEnv pending' origArg argType st rest emitted mergedEnv h_merge h1 h2
      · next h_not_err =>
        have h_ok : isEmptyOrError argVal = false ∨ argVal = origArg := by
          simp at h_not_err
          by_cases h_ie : isEmptyOrError argVal = true
          · exact Or.inr (h_not_err h_ie)
          · exact Or.inl (Bool.eq_false_iff.mpr h_ie)
        split
        · next h_ext =>
          exact .consumeBinderFail argVal evalEnv pending' origArg argType st rest emitted
            mergedEnv h_merge h_ok h_ext
        · next extEnv h_ext =>
          exact .consumeOk argVal evalEnv pending' origArg argType st rest emitted
            mergedEnv extEnv h_merge h_ok h_ext

/-- Frame processing realizes the step relation, regardless of how the frame
    was selected (policy-independent). -/
theorem processFrame_spec (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (frame : TypedApplyFrame) (rest : List TypedApplyFrame) (emitted : ResultList) :
    TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial
      ⟨frame :: rest, emitted⟩
      (processFrame eval1 applyEnv mergeEnv extendBinder isTrivial frame rest emitted) := by
  cases frame with
  | apply st => exact processApplyFrame_spec eval1 applyEnv mergeEnv extendBinder isTrivial st rest emitted
  | argConsumer pending origArg argType st =>
    exact processConsumerFrame_spec eval1 applyEnv mergeEnv extendBinder isTrivial
      pending origArg argType st rest emitted

def stepConfig (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) : TypedApplyConfig → TypedApplyConfig
  | ⟨[], emitted⟩ => ⟨[], emitted⟩
  | ⟨frame :: rest, emitted⟩ => processFrame eval1 applyEnv mergeEnv extendBinder isTrivial frame rest emitted

/-- The executable step function realizes the inductive step relation. -/
theorem stepConfig_spec (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg : TypedApplyConfig) (h : cfg.worklist ≠ []) :
    TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg
      (stepConfig eval1 applyEnv mergeEnv extendBinder isTrivial cfg) := by
  obtain ⟨worklist, emitted⟩ := cfg
  cases worklist with
  | nil => exact absurd rfl h
  | cons frame rest => exact processFrame_spec eval1 applyEnv mergeEnv extendBinder isTrivial frame rest emitted

def TypedApplyConfig.isDone (cfg : TypedApplyConfig) : Bool := cfg.worklist.isEmpty

def machineRun (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (cfg : TypedApplyConfig) (fuel : Nat) : TypedApplyConfig :=
  match fuel with
  | 0 => cfg
  | n + 1 =>
    if cfg.isDone then cfg
    else machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
           (stepConfig eval1 applyEnv mergeEnv extendBinder isTrivial cfg) n

/-- The fuel-indexed runner induces a reachability trace. -/
theorem machineRun_reaches (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg : TypedApplyConfig) (fuel : Nat) :
    TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg
      (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg fuel) := by
  induction fuel generalizing cfg with
  | zero => exact .refl
  | succ n ih =>
    simp only [machineRun]; split
    · exact .refl
    · next h =>
      have h_ne : cfg.worklist ≠ [] := by
        simp [TypedApplyConfig.isDone, List.isEmpty_iff] at h; exact h
      exact .step (stepConfig_spec _ _ _ _ _ cfg h_ne) (ih _)

/-! ## Target Safety: All TypedApply Frames Are Owned

Every `TypedApplyFrame` is owned state — it carries its own `TypedApplyState`
and `ResultList` with no borrowed references to stack-local data. This means
ALL typed-apply frames are `ownedResumeSafe` in the target-safety model.

This connects `TypedApplyMachine` to `OwnershipInvariant`: the machine
only creates frames that satisfy the running-stack contract. -/

/-- Every TypedApplyFrame is owned-resume-safe: it carries only owned data
    (TypedApplyState, ResultList, Atom), no borrowed stack-local pointers.

    In C: both `NATIVE_RESUME_FRAME_TYPED_APPLY` and
    `NATIVE_RESUME_FRAME_TYPED_ARG_CONSUMER` use malloc'd
    `NativeTypedApplyState`. -/
def TypedApplyFrame.safety : TypedApplyFrame → TargetSafety
  | .apply _ => TargetSafety.ownedResumeSafe
  | .argConsumer _ _ _ _ => TargetSafety.ownedResumeSafe

/-- All typed-apply frames can be deferred onto a running stack. -/
theorem TypedApplyFrame.canDefer (frame : TypedApplyFrame) :
    frame.safety.canDefer = true := by
  cases frame <;> rfl

/-- The typed-apply machine's worklist satisfies `DeferSafe` at every step:
    every frame in the worklist is `ownedResumeSafe`. -/
def TypedApplyDeferSafe (cfg : TypedApplyConfig) : Prop :=
  ∀ f, f ∈ cfg.worklist → f.safety = TargetSafety.ownedResumeSafe

theorem typedApplyDeferSafe_initial (st : TypedApplyState) :
    TypedApplyDeferSafe (.initial st) := by
  intro f hf; simp [TypedApplyConfig.initial] at hf; subst hf; rfl

/-- processFrame only creates ownedResumeSafe frames. Therefore
    TypedApplyDeferSafe is preserved by every machine step. -/
theorem typedApplyDeferSafe_step (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hSafe : TypedApplyDeferSafe cfg)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    TypedApplyDeferSafe cfg' := by
  intro f hf
  -- Every step constructor either:
  -- (a) removes frames from the worklist (preserves safety trivially)
  -- (b) adds .apply or .argConsumer frames (both ownedResumeSafe)
  cases hStep with
  | applyComplete _ rest _ _ => exact hSafe f (by simp [hf])
  | applyTrivialOk _ _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl
    · exact hSafe f (by simp [hf])
  | applyTrivialFail _ _ _ _ _ _ _ _ _ _ => exact hSafe f (by simp [hf])
  | applyEval _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl  -- new .argConsumer frame
    · exact hSafe f (by simp [hf])
  | consumeMergeFail _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl  -- same .argConsumer (trimmed)
    · exact hSafe f (by simp [hf])
  | consumeError _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl
    · exact hSafe f (by simp [hf])
  | consumeBinderFail _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl
    · exact hSafe f (by simp [hf])
  | consumeOk _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp at hf; rcases hf with rfl | hf
    · rfl  -- new .apply frame
    · rcases hf with rfl | hf
      · rfl  -- same .argConsumer (trimmed)
      · exact hSafe f (by simp [hf])
  | consumeExhausted _ _ _ _ _ => exact hSafe f (by simp [hf])

/-- TypedApplyDeferSafe is preserved across reachability. -/
theorem typedApplyDeferSafe_reaches (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hSafe : TypedApplyDeferSafe cfg)
    (hReach : TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    TypedApplyDeferSafe cfg' := by
  induction hReach with
  | refl => exact hSafe
  | step hs _ ih => exact ih (typedApplyDeferSafe_step _ _ _ _ _ _ _ hSafe hs)

/-! ## CeTTa Frame Kind Classification (Step 2: all 11 kinds)

CeTTa's drain loop has 11 frame kinds. Each must be classified as
ownedResumeSafe or not. This is the formal version of Codex's
"audit remaining `running_depth > 0` sites" task.

| C Frame Kind | Safety | Reason |
|-------------|--------|--------|
| EVAL | ownedResumeSafe | carries owned Atom + Bindings |
| MATCH_SOURCE_SIMPLE | ownedResumeSafe | owned match state |
| DELIVER | ownedResumeSafe | owned delivery target |
| SELECT_CONSUMER | ownedResumeSafe | malloc'd NativeSelectConsumerState |
| LET_CONSUMER | ownedResumeSafe | malloc'd NativeLetConsumerState |
| CHAIN_CONSUMER | ownedResumeSafe | malloc'd |
| IF_CONSUMER | ownedResumeSafe | malloc'd |
| COLLAPSE_CONSUMER | ownedResumeSafe | malloc'd |
| FUNCTION_CONSUMER | ownedResumeSafe | malloc'd |
| CASE_CONSUMER | ownedResumeSafe | malloc'd |
| TYPED_APPLY | ownedResumeSafe | malloc'd NativeTypedApplyState |

All 11 frame kinds are ownedResumeSafe because Codex's contract cleanup
ensures: only malloc'd owned state is stored in frame.owned_state,
and the frame itself is on the NativeResumeStack heap array. -/

/-! ## Emission Soundness

Each machine step either preserves existing emissions unchanged,
or appends exactly one result that falls into one of two categories:
1. A reconstructed call term `(head :: evArgs)` (from `applyComplete`)
2. An error short-circuit `(argVal, mergedEnv)` (from `consumeError`)

This is the structural lemma connecting machine emissions to semantics. -/

/-- Classification of what a step emits. -/
inductive EmittedKind where
  /-- A fully reconstructed call term: all args evaluated, assembled into (head arg0 ... argN). -/
  | callTerm (head : Atom) (evArgs : List Atom) (env : Bindings)
  /-- An error short-circuit: arg evaluated to a changed error/empty. -/
  | errorShortCircuit (argVal : Atom) (env : Bindings)
  deriving Repr

/-- Extract the result pair from an emission kind. -/
def EmittedKind.toResultPair : EmittedKind → ResultPair
  | .callTerm head evArgs env => (.expression (head :: evArgs), env)
  | .errorShortCircuit argVal env => (argVal, env)

/-- Every machine step either preserves emissions or appends one classified result. -/
theorem step_emits_sound
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (cfg cfg' : TypedApplyConfig)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    -- Either emissions are unchanged...
    cfg'.emitted = cfg.emitted ∨
    -- ...or exactly one result was appended, and it's classifiable
    (∃ kind : EmittedKind, cfg'.emitted = cfg.emitted ++ [kind.toResultPair]) := by
  cases hStep with
  | applyComplete st rest emitted h =>
    right; exact ⟨.callTerm st.headAtom st.evArgs st.env, rfl⟩
  | applyTrivialOk _ _ _ _ _ _ _ _ _ _ _ => left; rfl
  | applyTrivialFail _ _ _ _ _ _ _ _ _ _ => left; rfl
  | applyEval _ _ _ _ _ _ _ _ _ _ _ _ _ => left; rfl
  | consumeMergeFail _ _ _ _ _ _ _ _ _ => left; rfl
  | consumeError argVal evalEnv _ _ _ _ _ emitted mergedEnv _ _ _ =>
    right; exact ⟨.errorShortCircuit argVal mergedEnv, rfl⟩
  | consumeBinderFail _ _ _ _ _ _ _ _ _ _ _ _ => left; rfl
  | consumeOk _ _ _ _ _ _ _ _ _ _ _ _ => left; rfl
  | consumeExhausted _ _ _ _ _ => left; rfl

/-- Emissions only grow: every result in cfg.emitted stays in cfg'.emitted. -/
theorem step_emitted_monotone
    (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    ∀ r, r ∈ cfg.emitted → r ∈ cfg'.emitted := by
  intro r hr
  rcases step_emits_sound eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg' hStep with h | ⟨_, h⟩
  · rw [h]; exact hr
  · rw [h]; exact List.mem_append_left _ hr

/-- Emissions are monotone across reachability. -/
theorem emitted_monotone_reaches
    (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hReach : TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg') :
    ∀ r, r ∈ cfg.emitted → r ∈ cfg'.emitted := by
  induction hReach with
  | refl => intro r hr; exact hr
  | step hs _ ih =>
    intro r hr
    exact ih r (step_emitted_monotone _ _ _ _ _ _ _ hs r hr)

/-- A newly emitted result (not in the previous emissions) must be either
    a call-term reconstruction or an error short-circuit. -/
theorem new_emission_classified
    (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg')
    (r : ResultPair) (h_new : r ∈ cfg'.emitted) (h_not_old : r ∉ cfg.emitted) :
    ∃ kind : EmittedKind, r = kind.toResultPair := by
  rcases step_emits_sound eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg' hStep with h | ⟨kind, h⟩
  · rw [h] at h_new; exact absurd h_new h_not_old
  · rw [h] at h_new
    rw [List.mem_append] at h_new
    rcases h_new with h_old | h_eq
    · exact absurd h_old h_not_old
    · rw [List.mem_singleton] at h_eq; exact ⟨kind, h_eq⟩

/-! ## Call-Term Correctness

These lemmas connect machine emissions to semantic well-formedness.
They are rungs toward the full `emitted → InterpretArgs` soundness. -/

/-- When applyComplete fires, the emitted call term has the right arity:
    exactly origArgs.length + 1 elements (head + one per original arg).
    This is the key structural property: the machine evaluated ALL args. -/
theorem applyComplete_arity (st : TypedApplyState)
    (h_prefix : st.evArgs.length = st.idx)
    (h_done : st.idx ≥ st.origArgs.length) :
    (st.headAtom :: st.evArgs).length ≥ st.origArgs.length + 1 := by
  simp; omega

/-- The evaluated args list has at least as many elements as the original. -/
theorem applyComplete_evArgs_length (st : TypedApplyState)
    (h_prefix : st.evArgs.length = st.idx)
    (h_done : st.idx ≥ st.origArgs.length) :
    st.evArgs.length ≥ st.origArgs.length := by omega

/-- With well-formedness (idx ≤ origArgs.length), arity is EXACT. -/
theorem applyComplete_arity_exact (st : TypedApplyState)
    (h_prefix : st.evArgs.length = st.idx)
    (h_done : st.idx ≥ st.origArgs.length)
    (h_wf : st.idx ≤ st.origArgs.length) :
    st.evArgs.length = st.origArgs.length := by omega


/-- Combined: every new emission from ANY step is well-formed.
    Call terms have correct arity (given PrefixInvariant).
    Error results satisfy isEmptyOrError. -/
theorem new_emission_wellformed
    (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg cfg' : TypedApplyConfig)
    (hStep : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial cfg cfg')
    (hPrefix : PrefixInvariant cfg)
    (r : ResultPair) (h_new : r ∈ cfg'.emitted) (h_old : r ∉ cfg.emitted) :
    -- The result is either a correctly-sized call term or an error
    (∃ head evArgs env,
       r = (.expression (head :: evArgs), env) ∧
       ∃ st : TypedApplyState,
         st.headAtom = head ∧ st.evArgs = evArgs ∧ st.env = env ∧
         evArgs.length ≥ st.origArgs.length) ∨
    (∃ argVal env, r = (argVal, env) ∧ isEmptyOrError argVal = true) := by
  -- Only applyComplete and consumeError add to emitted
  cases hStep with
  | applyComplete st rest emitted h_done =>
    left
    simp [List.mem_append] at h_new
    rcases h_new with h | h
    · exact absurd h h_old
    · exact ⟨st.headAtom, st.evArgs, st.env, h, st, rfl, rfl, rfl,
             by have := hPrefix (TypedApplyFrame.apply st) (by simp); simp at this; omega⟩
  | consumeError argVal evalEnv pending origArg argType st rest emitted mergedEnv h_mg h_err h_changed =>
    right
    simp [List.mem_append] at h_new
    rcases h_new with h | h
    · exact absurd h h_old
    · exact ⟨argVal, mergedEnv, h, h_err⟩
  -- All other constructors don't change emitted
  | applyTrivialOk _ _ _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | applyTrivialFail _ _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | applyEval _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | consumeMergeFail _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | consumeBinderFail _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | consumeOk _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)
  | consumeExhausted _ _ _ _ _ => exact absurd h_new (by simp; exact h_old)

/-! ## Per-Position Arg Provenance

Tracks HOW each evArgs[i] was produced from origArgs[i]. This is the
key invariant connecting the machine's accumulated state back to the
original arguments — the rung below `emitted → InterpretArgs`. -/

/-- How one evaluated argument was produced. -/
inductive ArgProvenance
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom) where
  /-- Fast path: variable substitution only, no eval1 call.
      C: `atom_is_symbol_id(arg_type, atom) || orig_arg->kind == ATOM_VAR` -/
  | fastPath (origArg : Atom) (env : Bindings)
      (h : evArg = applyEnv env origArg) : ArgProvenance eval1 applyEnv
  /-- Eval path: result came from eval1 on the bound argument.
      C: `metta_eval_bind_typed_on_stack(...)` -/
  | evalResult (origArg argType : Atom) (env evalEnv : Bindings)
      (h_mem : (evArg, evalEnv) ∈ eval1 (applyEnv env origArg) argType env) :
      ArgProvenance eval1 applyEnv

/-- The provenance invariant: for each position i < idx, evArgs[i] was
    produced from origArgs[i] through either the fast path or eval path.

    This is stated as: the evArgs list, together with origArgs, satisfies
    a pointwise provenance relation. -/
def ProvenanceInvariant
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (st : TypedApplyState) : Prop :=
  st.evArgs.length = st.idx ∧
  ∀ i (hi : i < st.evArgs.length) (ho : i < st.origArgs.length),
    ∃ env : Bindings,
      -- evArgs[i] came from origArgs[i] via one of the two paths
      (st.evArgs[i] = applyEnv env st.origArgs[i]) ∨
      (∃ argType evalEnv,
        (st.evArgs[i], evalEnv) ∈ eval1 (applyEnv env st.origArgs[i]) argType env)

/-- Initial state satisfies provenance (vacuously: no evArgs yet). -/
theorem provenance_initial
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (head : Atom) (args types : List Atom) (env : Bindings) :
    ProvenanceInvariant eval1 applyEnv (.initial head args types env) := by
  constructor
  · rfl
  · intro i hi; simp [TypedApplyState.initial] at hi

/-- Advancing with a fast-path argument preserves provenance. -/
theorem provenance_advance_fast
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (st : TypedApplyState)
    (h_prov : ProvenanceInvariant eval1 applyEnv st)
    (h_lt : st.idx < st.origArgs.length)
    (env' : Bindings)
    (boundArg : Atom) (h_bound : boundArg = applyEnv st.env st.origArgs[st.idx]) :
    ProvenanceInvariant eval1 applyEnv (st.advance boundArg env') := by
  obtain ⟨h_len, h_pos⟩ := h_prov
  constructor
  · simp [TypedApplyState.advance, h_len]
  · intro i hi ho
    simp [TypedApplyState.advance] at hi
    simp only [TypedApplyState.advance] at hi ho ⊢
    by_cases h_last : i < st.evArgs.length
    · -- Old position: use existing provenance
      rw [List.getElem_append_left h_last]
      exact h_pos i h_last (by omega)
    · -- New position: i = st.evArgs.length = st.idx
      have h_eq : i = st.evArgs.length := by omega
      subst h_eq
      rw [List.getElem_append_right (by omega)]
      simp [h_bound, h_len]
      exact ⟨st.env, Or.inl rfl⟩

/-- Advancing with an eval-path argument preserves provenance. -/
theorem provenance_advance_eval
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (st : TypedApplyState)
    (h_prov : ProvenanceInvariant eval1 applyEnv st)
    (h_lt : st.idx < st.origArgs.length)
    (argVal : Atom) (evalEnv : Bindings) (env' : Bindings)
    (argType : Atom)
    (h_mem : (argVal, evalEnv) ∈ eval1 (applyEnv st.env st.origArgs[st.idx]) argType st.env) :
    ProvenanceInvariant eval1 applyEnv (st.advance argVal env') := by
  obtain ⟨h_len, h_pos⟩ := h_prov
  constructor
  · simp [TypedApplyState.advance, h_len]
  · intro i hi ho
    simp only [TypedApplyState.advance] at hi ho ⊢
    by_cases h_last : i < st.evArgs.length
    · rw [List.getElem_append_left h_last]
      exact h_pos i h_last (by omega)
    · have h_app_len : (st.evArgs ++ [argVal]).length = st.evArgs.length + 1 := by simp
      have h_eq : i = st.evArgs.length := by omega
      subst h_eq
      rw [List.getElem_append_right (by omega)]
      simp [h_len]
      exact ⟨st.env, Or.inr ⟨argType, evalEnv, h_mem⟩⟩

/-! ## Emission-Spec Bridge

When the machine emits a call term `(head :: evArgs, env)` and provenance
holds, the emitted term has the structure that `InterpretArgs` would produce:
- head is the original operator
- evArgs has one element per original argument
- each element was produced from the corresponding original argument
- the bindings were threaded left-to-right through evaluation

This is the structural bridge between machine emissions and the EvalSpec.
The FULL `emitted → InterpretArgs` requires instantiating `eval1` as
`evalAtom` and using `Correctness.lean`'s soundness. This theorem gives
the structural precondition. -/

/-- When applyComplete fires with provenance + well-formedness, the emitted
    call term has:
    (a) correct head (= original operator)
    (b) correct arity (= origArgs.length arguments)
    (c) each argument position traced to its original -/
theorem applyComplete_sound_structure
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (st : TypedApplyState)
    (h_prov : ProvenanceInvariant eval1 applyEnv st)
    (h_done : st.idx ≥ st.origArgs.length)
    (h_wf : st.idx ≤ st.origArgs.length) :
    -- The emitted expression has the right head
    (st.headAtom :: st.evArgs).head? = some st.headAtom
    -- The emitted expression has the right arity
    ∧ st.evArgs.length = st.origArgs.length
    -- Every evaluated arg traces to its original
    ∧ ∀ i (hi : i < st.evArgs.length) (ho : i < st.origArgs.length),
        ∃ env : Bindings,
          (st.evArgs[i] = applyEnv env st.origArgs[i]) ∨
          (∃ argType evalEnv,
            (st.evArgs[i], evalEnv) ∈ eval1 (applyEnv env st.origArgs[i]) argType env) := by
  obtain ⟨h_len, h_pos⟩ := h_prov
  exact ⟨rfl, by omega, h_pos⟩

/-! ## Invariant Summary

The typed-apply machine now has 7 proved invariants:

| Invariant | Theorem | What it guarantees |
|-----------|---------|-------------------|
| Prefix length | `prefixInvariant_step` | evArgs.length = idx |
| Target safety | `typedApplyDeferSafe_step` | All frames are ownedResumeSafe |
| Binding consistency | `bindingsSafe_step` (BindingConsistency.lean) | No binding loops |
| Emission classification | `step_emits_sound` | callTerm or errorShortCircuit |
| Emission monotonicity | `step_emitted_monotone` | Old results persist |
| Emission well-formedness | `new_emission_wellformed` | Correct arity + error flag |
| Arg provenance | `provenance_advance_fast/eval` | evArgs[i] from origArgs[i] |

Combined at completion (`applyComplete_sound_structure`):
- head is preserved
- arity is exact
- every arg traces to its source via eval1 or applyEnv

The remaining gap to full `emitted → InterpretArgs`:
instantiate eval1 = evalAtom, use Correctness.lean soundness to
convert each provenance witness into an EvalAtom derivation,
then assemble into an InterpretArgs derivation tree. -/

/-! ## Concrete Witness -/

example : TypedApplyStep
    (fun a _ b => [(a, b)]) (fun _ a => a) (fun _ b => some b) (fun b _ _ => some b) (fun _ => false)
    ⟨[.apply ⟨.symbol "f", [], [], 0, [], Bindings.empty⟩], []⟩
    ⟨[], [(.expression [.symbol "f"], Bindings.empty)]⟩ :=
  .applyComplete _ _ _ (Nat.le_refl _)

/-! ## Ordered residual correspondence

The direct evaluator and the worklist have separate definitions. A paused
consumer owns all of its remaining argument occurrences, including duplicates
and failure branches. Published occurrences followed by this residual have the
same meaning as direct typed application. This is stronger than membership or
bag soundness, and applies even when an administrative budget ends mid-call.
-/

/-- The direct continuation for an already completed argument frontier. -/
def typedConsumerDirect
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (pending : ResultList) (origArg argType : Atom) (st : TypedApplyState) : ResultList :=
  pending.flatMap fun (argVal, evalEnv) =>
    match mergeEnv st.env evalEnv with
    | none => []
    | some mergedEnv =>
      if isEmptyOrError argVal && decide (argVal ≠ origArg) then
        [(argVal, mergedEnv)]
      else
        match extendBinder mergedEnv argType argVal with
        | none => []
        | some extEnv =>
          typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial
            (st.advance argVal extEnv)

def TypedApplyFrame.meaning
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) :
    TypedApplyFrame → ResultList
  | .apply st => typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st
  | .argConsumer pending origArg argType st =>
      typedConsumerDirect eval1 applyEnv mergeEnv extendBinder isTrivial
        pending origArg argType st

/-- Observations already published, followed by the exact ordered residual. -/
def TypedApplyConfig.observations
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool)
    (cfg : TypedApplyConfig) : ResultList :=
  cfg.emitted ++ cfg.worklist.flatMap
    (TypedApplyFrame.meaning eval1 applyEnv mergeEnv extendBinder isTrivial)

theorem typedApplyStep_preserves_observations (eval1 applyEnv mergeEnv extendBinder isTrivial)
    {before after : TypedApplyConfig}
    (step : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial before after) :
    before.observations eval1 applyEnv mergeEnv extendBinder isTrivial =
      after.observations eval1 applyEnv mergeEnv extendBinder isTrivial := by
  cases step with
  | applyComplete st rest emitted done =>
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
        base_case eval1 applyEnv mergeEnv extendBinder isTrivial st done,
        List.append_assoc]
  | applyTrivialOk st rest emitted boundArg argType env' lt trivial bound typ extended =>
      have direct : typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st =
          typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial
            (st.advance boundArg env') := by
        conv_lhs => unfold typedApplyDirect
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← bound]
        simp [trivial, extended, TypedApplyState.advance]
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning, direct]
  | applyTrivialFail st rest emitted boundArg argType lt trivial bound typ extended =>
      have direct : typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st = [] := by
        conv_lhs => unfold typedApplyDirect
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← bound]
        simp [trivial, extended]
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning, direct]
  | applyEval st rest emitted origArg argType boundArg results lt nontrivial orig typ bound vals =>
      have direct : typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st =
          typedConsumerDirect eval1 applyEnv mergeEnv extendBinder isTrivial
            results origArg argType st := by
        conv_lhs => unfold typedApplyDirect
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← orig]
        have condition : (isTrivial argType || origArg.isVariable) = false := by
          simpa only [Bool.or_eq_false_iff, Bool.not_eq_true, not_or] using nontrivial
        simp only [condition, Bool.false_eq_true, ite_false]
        rw [← bound, ← vals]
        rfl
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning, direct]
  | consumeMergeFail argVal evalEnv pending origArg argType st rest emitted merged =>
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
        typedConsumerDirect, merged]
  | consumeError argVal evalEnv pending origArg argType st rest emitted mergedEnv merged err changed =>
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
        typedConsumerDirect, merged, err, changed, List.append_assoc]
  | consumeBinderFail argVal evalEnv pending origArg argType st rest emitted mergedEnv merged ok extended =>
      rcases ok with ok | rfl
      · simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
          typedConsumerDirect, merged, ok, extended]
      · simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
          typedConsumerDirect, merged, extended]
  | consumeOk argVal evalEnv pending origArg argType st rest emitted mergedEnv extEnv merged ok extended =>
      rcases ok with ok | rfl
      · simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
          typedConsumerDirect, merged, ok, extended, List.append_assoc]
      · simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
          typedConsumerDirect, merged, extended, List.append_assoc]
  | consumeExhausted origArg argType st rest emitted =>
      simp [TypedApplyConfig.observations, TypedApplyFrame.meaning, typedConsumerDirect]

theorem typedApplyReaches_preserves_observations (eval1 applyEnv mergeEnv extendBinder isTrivial)
    {before after : TypedApplyConfig}
    (run : TypedApplyReaches eval1 applyEnv mergeEnv extendBinder isTrivial before after) :
    before.observations eval1 applyEnv mergeEnv extendBinder isTrivial =
      after.observations eval1 applyEnv mergeEnv extendBinder isTrivial := by
  induction run with
  | refl => rfl
  | step one rest ih =>
      exact (typedApplyStep_preserves_observations _ _ _ _ _ one).trans ih

/-- Ending an administrative run early retains precisely the undelivered
suffix. The budget controls machine steps, not the argument evaluator's fuel. -/
theorem typedApplyMachine_budget_residual (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) (budget : Nat) :
    typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st =
      (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
        (.initial st) budget).observations eval1 applyEnv mergeEnv extendBinder isTrivial := by
  have conserved := typedApplyReaches_preserves_observations _ _ _ _ _
    (machineRun_reaches eval1 applyEnv mergeEnv extendBinder isTrivial (.initial st) budget)
  simpa [TypedApplyConfig.observations, TypedApplyConfig.initial, TypedApplyFrame.meaning]
    using conserved

/-- An exhausted machine publishes exactly the independent direct evaluator's
ordered occurrences and bindings. -/
theorem typedApplyMachine_complete_eq_direct (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) (budget : Nat)
    (done : (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
      (.initial st) budget).worklist = []) :
    (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
      (.initial st) budget).emitted =
        typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st := by
  simpa [TypedApplyConfig.observations, done] using
    (typedApplyMachine_budget_residual eval1 applyEnv mergeEnv extendBinder isTrivial
      st budget).symm

theorem typedApplyMachine_done_stable (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg : TypedApplyConfig) (budget : Nat) (done : cfg.isDone = true) :
    machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget = cfg := by
  cases budget <;> simp [machineRun, done]

/-- Resumption continues the saved machine rather than entering its original
source again. The two runs compose at their exact administrative budgets. -/
theorem typedApplyMachine_pause_resume (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (cfg : TypedApplyConfig) (first second : Nat) :
    machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg (first + second) =
      machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
        (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg first) second := by
  induction first generalizing cfg with
  | zero => simp [machineRun]
  | succ first ih =>
      by_cases done : cfg.isDone = true
      · rw [typedApplyMachine_done_stable _ _ _ _ _ cfg _ done,
            typedApplyMachine_done_stable _ _ _ _ _ cfg _ done,
            typedApplyMachine_done_stable _ _ _ _ _ cfg _ done]
      · simpa only [Nat.succ_add, machineRun, if_neg done] using
          ih (stepConfig eval1 applyEnv mergeEnv extendBinder isTrivial cfg)

/-- Cancellation at a saved boundary keeps an ordered prefix of the direct
observations. It cannot invent answers or erase an already delivered duplicate. -/
theorem typedApplyMachine_cancel_prefix (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) (budget : Nat) :
    ∃ residual : ResultList,
      typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st =
        (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
          (.initial st) budget).emitted ++ residual := by
  refine ⟨_, typedApplyMachine_budget_residual
    eval1 applyEnv mergeEnv extendBinder isTrivial st budget⟩

private def duplicateArgument : Atom → Atom → Bindings → ResultList :=
  fun _ _ env => [(.symbol "value", env), (.symbol "value", env)]

/-- Two equal argument occurrences produce two equal calls in source order. -/
theorem typedApplyMachine_duplicate_occurrences :
    (machineRun duplicateArgument (fun _ atom => atom)
      (fun _ env => some env) (fun env _ _ => some env) (fun _ => false)
      (.initial (.initial (.symbol "f") [.symbol "source"] [.symbol "T"] Bindings.empty))
      6).emitted =
    [(.expression [.symbol "f", .symbol "value"], Bindings.empty),
     (.expression [.symbol "f", .symbol "value"], Bindings.empty)] := by
  decide

/-- A consumer that throws away its second pending occurrence is observably
different, even when both occurrences contain the same atom and bindings. -/
theorem typedApplyMachine_dropped_duplicate_changes_observation :
    TypedApplyConfig.observations duplicateArgument (fun _ atom => atom)
      (fun _ env => some env) (fun env _ _ => some env) (fun _ => false)
      ⟨[.argConsumer [(.symbol "value", Bindings.empty), (.symbol "value", Bindings.empty)]
        (.symbol "source") (.symbol "T")
        (.initial (.symbol "f") [.symbol "source"] [.symbol "T"] Bindings.empty)], []⟩ ≠
    TypedApplyConfig.observations duplicateArgument (fun _ atom => atom)
      (fun _ env => some env) (fun env _ _ => some env) (fun _ => false)
      ⟨[.argConsumer [(.symbol "value", Bindings.empty)]
        (.symbol "source") (.symbol "T")
        (.initial (.symbol "f") [.symbol "source"] [.symbol "T"] Bindings.empty)], []⟩ := by
  simp [TypedApplyConfig.observations, TypedApplyFrame.meaning,
    typedConsumerDirect, typedApplyDirect, TypedApplyState.initial,
    TypedApplyState.advance, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]

/-! ## Administrative and argument-service work

The potential is the work of the independently defined recursive argument
tree, including every failed and successful consumer occurrence. An argument
service's supplied cost is charged at `applyEval`; every other transition is
one administrative step. This account does not equate administrative fuel
with the dialect evaluator's fuel or assume that a native service is free.
-/

def typedConsumerWork
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) (evalCost : Atom → Atom → Bindings → Nat)
    (pending : ResultList) (origArg argType : Atom) (st : TypedApplyState) : Nat :=
  1 + (pending.map fun (argVal, evalEnv) =>
    1 + match mergeEnv st.env evalEnv with
    | none => 0
    | some mergedEnv =>
      if isEmptyOrError argVal && decide (argVal ≠ origArg) then 0
      else
        match extendBinder mergedEnv argType argVal with
        | none => 0
        | some extEnv => typedApplyWork eval1 applyEnv mergeEnv extendBinder
            isTrivial evalCost (st.advance argVal extEnv)).sum

def TypedApplyFrame.work
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) (evalCost : Atom → Atom → Bindings → Nat) :
    TypedApplyFrame → Nat
  | .apply st => typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost st
  | .argConsumer pending origArg argType st =>
      typedConsumerWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost
        pending origArg argType st

def TypedApplyConfig.work
    (eval1 : Atom → Atom → Bindings → ResultList)
    (applyEnv : Bindings → Atom → Atom)
    (mergeEnv : Bindings → Bindings → Option Bindings)
    (extendBinder : Bindings → Atom → Atom → Option Bindings)
    (isTrivial : Atom → Bool) (evalCost : Atom → Atom → Bindings → Nat)
    (cfg : TypedApplyConfig) : Nat :=
  (cfg.worklist.map (TypedApplyFrame.work
    eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)).sum

def TypedApplyConfig.serviceCost (applyEnv : Bindings → Atom → Atom)
    (isTrivial : Atom → Bool) (evalCost : Atom → Atom → Bindings → Nat)
    (cfg : TypedApplyConfig) : Nat :=
  match cfg.worklist with
  | .apply st :: _ =>
      if h : st.idx < st.origArgs.length then
        if isTrivial (getArgType st) || st.origArgs[st.idx].isVariable then 0
        else evalCost (applyEnv st.env st.origArgs[st.idx]) (getArgType st) st.env
      else 0
  | _ => 0

theorem typedApplyStep_work (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    {before after : TypedApplyConfig}
    (step : TypedApplyStep eval1 applyEnv mergeEnv extendBinder isTrivial before after) :
    before.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost =
      1 + before.serviceCost applyEnv isTrivial evalCost +
        after.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost := by
  cases step with
  | applyComplete st rest emitted done =>
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        typedApplyWork, done]
  | applyTrivialOk st rest emitted boundArg argType env' lt trivial bound typ extended =>
      have direct : typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost st =
          1 + typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost
            (st.advance boundArg env') := by
        conv_lhs => unfold typedApplyWork
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← bound]
        simp [trivial, extended, TypedApplyState.advance]
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        direct, getArgType, lt, ← typ, trivial, Nat.add_assoc]
  | applyTrivialFail st rest emitted boundArg argType lt trivial bound typ extended =>
      have direct : typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost st = 1 := by
        conv_lhs => unfold typedApplyWork
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← bound]
        simp [trivial, extended]
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        direct, getArgType, lt, ← typ, trivial]
  | applyEval st rest emitted origArg argType boundArg results lt nontrivial orig typ bound vals =>
      have direct : typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost st =
          1 + evalCost boundArg argType st.env +
            typedConsumerWork eval1 applyEnv mergeEnv extendBinder isTrivial evalCost
              results origArg argType st := by
        conv_lhs => unfold typedApplyWork
        simp only [show ¬st.idx ≥ st.origArgs.length by omega, dite_false]
        rw [← typ, ← orig]
        have condition : (isTrivial argType || origArg.isVariable) = false := by
          simpa only [Bool.or_eq_false_iff, Bool.not_eq_true, not_or] using nontrivial
        simp only [condition, Bool.false_eq_true, ite_false]
        rw [← bound, ← vals]
        simp only [typedConsumerWork, TypedApplyState.advance]
        change (1 + 1) + _ + _ = 1 + _ + (1 + _)
        ac_rfl
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        direct, getArgType, lt, ← typ, ← orig, nontrivial, bound, Nat.add_assoc]
  | consumeMergeFail argVal evalEnv pending origArg argType st rest emitted merged =>
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        typedConsumerWork, merged, Nat.add_left_comm, Nat.add_comm]
  | consumeError argVal evalEnv pending origArg argType st rest emitted mergedEnv merged err changed =>
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        typedConsumerWork, merged, err, changed,
        Nat.add_left_comm, Nat.add_comm]
  | consumeBinderFail argVal evalEnv pending origArg argType st rest emitted mergedEnv merged ok extended =>
      rcases ok with ok | rfl
      · simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
          typedConsumerWork, merged, ok, extended,
          Nat.add_left_comm, Nat.add_comm]
      · simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
          typedConsumerWork, merged, extended,
          Nat.add_left_comm, Nat.add_comm]
  | consumeOk argVal evalEnv pending origArg argType st rest emitted mergedEnv extEnv merged ok extended =>
      rcases ok with ok | rfl
      · simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
          typedConsumerWork, merged, ok, extended,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
          typedConsumerWork, merged, extended,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | consumeExhausted origArg argType st rest emitted =>
      simp [TypedApplyConfig.work, TypedApplyFrame.work, TypedApplyConfig.serviceCost,
        typedConsumerWork]

theorem typedApplyFrame_work_positive (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (frame : TypedApplyFrame) :
    0 < frame.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost := by
  cases frame with
  | apply st => exact typedApplyWork_positive _ _ _ _ _ _ st
  | argConsumer pending origArg argType st =>
      simp only [TypedApplyFrame.work, typedConsumerWork]
      omega

theorem typedApplyConfig_work_zero_iff (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) :
    cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost = 0 ↔ cfg.worklist = [] := by
  cases cfg with
  | mk worklist emitted =>
      cases worklist with
      | nil => simp [TypedApplyConfig.work]
      | cons frame rest =>
          have positive := typedApplyFrame_work_positive
            eval1 applyEnv mergeEnv extendBinder isTrivial evalCost frame
          simp only [TypedApplyConfig.work, List.map_cons, List.sum_cons,
            List.cons_ne_nil, iff_false]
          omega

/-- Each live continuation contributes positive work to the independently
defined argument tree. Thus a width of pending alternatives cannot create
unaccounted frames. This bounds frames, not the bytes of their reachable data. -/
theorem typedApplyConfig_frames_le_work (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) :
    cfg.worklist.length ≤ cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost := by
  rcases cfg with ⟨frames, emitted⟩
  induction frames with
  | nil => simp [TypedApplyConfig.work]
  | cons frame rest ih =>
      have positive := typedApplyFrame_work_positive
        eval1 applyEnv mergeEnv extendBinder isTrivial evalCost frame
      simp only [List.length_cons, TypedApplyConfig.work, List.map_cons, List.sum_cons] at *
      omega

theorem typedApplyMachine_work_le (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) (budget : Nat) :
    (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).work
        eval1 applyEnv mergeEnv extendBinder isTrivial evalCost ≤
      cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost := by
  induction budget generalizing cfg with
  | zero => simp [machineRun]
  | succ budget ih =>
      by_cases done : cfg.isDone = true
      · simp [machineRun, done]
      · have pending : cfg.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have decreases := typedApplyStep_work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost
          (stepConfig_spec eval1 applyEnv mergeEnv extendBinder isTrivial cfg pending)
        simpa [machineRun, done] using (ih
          (stepConfig eval1 applyEnv mergeEnv extendBinder isTrivial cfg)).trans (by omega)

/-- Every paused frontier's frame count is bounded by the original direct
tree's work account, even when service evaluation returns duplicates. -/
theorem typedApplyMachine_frontier_bound (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) (budget : Nat) :
    (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).worklist.length ≤
      cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost :=
  (typedApplyConfig_frames_le_work _ _ _ _ _ _ _).trans
    (typedApplyMachine_work_le _ _ _ _ _ _ _ _)

theorem typedApplyMachine_complete_of_work_le (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) (budget : Nat)
    (enough : cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost ≤ budget) :
    (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).worklist = [] := by
  induction budget generalizing cfg with
  | zero =>
      have done := (typedApplyConfig_work_zero_iff
        eval1 applyEnv mergeEnv extendBinder isTrivial evalCost cfg).mp (by omega)
      simpa [machineRun] using done
  | succ budget ih =>
      by_cases done : cfg.isDone = true
      · simpa [typedApplyMachine_done_stable _ _ _ _ _ cfg _ done,
          TypedApplyConfig.isDone] using done
      · have pending : cfg.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have decreases := typedApplyStep_work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost
          (stepConfig_spec eval1 applyEnv mergeEnv extendBinder isTrivial cfg pending)
        simpa [machineRun, done] using ih
          (stepConfig eval1 applyEnv mergeEnv extendBinder isTrivial cfg) (by omega)

/-- Zero argument-service charges give an administrative completion budget
derived from the independent direct tree, not from running the same machine. -/
theorem typedApplyMachine_work_budget_eq_direct (eval1 applyEnv mergeEnv extendBinder isTrivial)
    (st : TypedApplyState) :
    (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial (.initial st)
      (typedApplyWork eval1 applyEnv mergeEnv extendBinder isTrivial (fun _ _ _ => 0) st)).emitted =
        typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st := by
  apply typedApplyMachine_complete_eq_direct
  apply typedApplyMachine_complete_of_work_le _ _ _ _ _ (fun _ _ _ => 0)
  simp [TypedApplyConfig.work, TypedApplyConfig.initial, TypedApplyFrame.work]

/-! ## Native roots of the typed argument frontier

Each logical argument frame is assigned its native field inventory. This
connects the independent direct-tree work bound to graph retention; bytes and
transitive descendants remain explicit, as a small number of roots can reach a
large graph. The inventory function is a native correspondence parameter, not a
claim that C root discovery follows from the abstract machine alone.
-/

def TypedApplyConfig.ownedFrontier {Address : Type}
    (inventory : TypedApplyFrame → HeOwnedRoots Address)
    (cfg : TypedApplyConfig) : HeOwnedFrontier Address :=
  cfg.worklist.zipIdx.map fun entry => (entry.2, inventory entry.1)

theorem typedApplyConfig_ownedFrontier_length {Address : Type}
    (inventory : TypedApplyFrame → HeOwnedRoots Address) (cfg : TypedApplyConfig) :
    (cfg.ownedFrontier inventory).length = cfg.worklist.length := by
  simp [TypedApplyConfig.ownedFrontier]

open Mettapedia.Machines.ResourceOwnership in
/-- Paused storage is bounded by independently accounted argument-tree work,
including both native frame headers and every transitively retained payload. -/
theorem typedApplyMachine_retention_bound {Address Value : Type} [DecidableEq Address]
    (eval1 applyEnv mergeEnv extendBinder isTrivial evalCost)
    (cfg : TypedApplyConfig) (budget : Nat) (heap : Heap Address Value)
    (inventory : TypedApplyFrame → HeOwnedRoots Address)
    (slots descendants payloadBytes frameBytes : Nat)
    (slotBound : ∀ frame ∈
      (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).worklist,
      (inventory frame).slots.length ≤ slots)
    (descendantBound : ∀ pair ∈ heFrontierRoots
      ((machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).ownedFrontier inventory),
      (footprint heap {pair}).card ≤ descendants)
    (byteBound : ∀ a ∈ footprint heap (heFrontierRoots
      ((machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).ownedFrontier inventory)),
      cellBytes heap a ≤ payloadBytes) :
    retainedBytes heap (heFrontierRoots
      ((machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).ownedFrontier inventory)) +
        (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget).worklist.length * frameBytes ≤
      cfg.work eval1 applyEnv mergeEnv extendBinder isTrivial evalCost *
        (slots * descendants * payloadBytes + frameBytes) := by
  let paused := machineRun eval1 applyEnv mergeEnv extendBinder isTrivial cfg budget
  have fields : ∀ entry ∈ paused.ownedFrontier inventory, entry.2.slots.length ≤ slots := by
    intro entry member
    obtain ⟨original, present, equal⟩ := List.mem_map.mp member
    subst entry
    exact slotBound original.1 (List.fst_mem_of_mem_zipIdx present)
  have retained := heFrontier_retention_bound heap (paused.ownedFrontier inventory)
    slots descendants payloadBytes fields descendantBound byteBound
  rw [typedApplyConfig_ownedFrontier_length] at retained
  have frames := typedApplyMachine_frontier_bound
    eval1 applyEnv mergeEnv extendBinder isTrivial evalCost cfg budget
  calc
    _ ≤ paused.worklist.length * slots * descendants * payloadBytes +
        paused.worklist.length * frameBytes := Nat.add_le_add_right retained _
    _ = paused.worklist.length * (slots * descendants * payloadBytes + frameBytes) := by
      simp only [Nat.mul_add, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ frames

end Mettapedia.Languages.MeTTa.HE
