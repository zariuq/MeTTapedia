import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDependentComputation

/-!
# Native dependent results of raw scoped computation code

Three finite operations mark the selected private state or return native
reflexivity at their argument. Their signatures, raw handlers and primitive
world lists are authored independently. Signature formation, source typing,
exact handler realization and result typing are separate proofs.

The source binds the result of an effectful choice and calls reflexivity at
that selected native value, retaining both in a native Sigma pair. Its answers
are raw terms, not proof-carrying answer subtypes. Resetting continuation state
changes the intents, and another branch's reflexivity does not have the
selected result type. This is the scoped sequencing fragment, not a full
CBPV calculus or a lazy binding implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation.NativeExamples

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

inductive Operation where
  | markTrue
  | markFalse
  | reflexivity
  deriving DecidableEq, Repr

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def signature : OperationSignature Tower.Head Operation where
  input _ := ground
  output
    | .markTrue => ground
    | .markFalse => ground
    | .reflexivity => .id ground (.var 0) (.var 0)

/-- Each authored declaration is formed by the native refined rules. -/
theorem operation_formation (operation : Operation) :
    OperationFormation Tower.rules signature operation := by
  constructor
  · exact ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩
  · cases operation with
    | markTrue => exact ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩
    | markFalse => exact ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩
    | reflexivity =>
        exact ⟨.sort Tower.zero, .sort Tower.zero,
          .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩

def context : Tower.Ctx 2 := .snoc (.snoc .nil ground) ground

theorem context_formed : FormationSensitive.ContextFormation Tower.rules context :=
  .snoc (.snoc .nil (.headType .legacyGround) (.sort Tower.zero))
    (.headType .legacyGround) (.sort Tower.zero)

def older : Tower.Tm 2 := .var 1
def newer : Tower.Tm 2 := .var 0

def identityFamily : Tower.Tm 3 := .id ground (.var 0) (.var 0)

theorem sigma_formed : FormationSensitive.Typing Tower.rules context
    (.sigma ground identityFamily) (sortTm (.max Tower.zero Tower.zero)) :=
  .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

def first : Code Tower.Head Operation 2 :=
  .choose (.call .markTrue older) (.call .markFalse newer)

def body : Code Tower.Head Operation 3 := .call .reflexivity (.var 0)

def source : Code Tower.Head Operation 2 := .sequenceSigma first body

theorem first_typing : Typing Tower.rules signature context first ground := by
  exact .choose
    (.call (operation_formation .markTrue) (.var 1))
    (.call (operation_formation .markFalse) (.var 0))

theorem body_typing :
    Typing Tower.rules signature (.snoc context ground) body identityFamily := by
  exact .call (operation_formation .reflexivity) (.var 0)

/-- Raw authored code is admitted independently of its implementation. -/
theorem source_typing :
    Typing Tower.rules signature context source (.sigma ground identityFamily) :=
  .sequenceSigma sigma_formed (.sort _) first_typing body_typing

theorem source_judgment :
    Judgment Tower.rules signature context source (.sigma ground identityFamily) :=
  ⟨context_formed, source_typing⟩

/-- A raw handler: no formation or admission proofs occur in its answers. -/
def handler {n : Nat} : Operation → Tower.Tm n → Program Bool (Tower.Tm n) Nat
  | .markTrue, argument => .write true (.intent 10 (.pure argument))
  | .markFalse, argument => .write false (.intent 20 (.pure argument))
  | .reflexivity, argument =>
      .read fun state => .intent (if state then 30 else 40) (.pure (.refl argument))

/-- Independently authored primitive world semantics, with no call to the
contextual handler or its evaluator. -/
def primitiveWorlds {n : Nat} : Operation → Tower.Tm n → Bool → BranchTrace →
    List (WorldResult Bool (Tower.Tm n) Nat)
  | .markTrue, argument, _, branch =>
      [{ branch := branch, answer := argument, state := true, intents := [10] }]
  | .markFalse, argument, _, branch =>
      [{ branch := branch, answer := argument, state := false, intents := [20] }]
  | .reflexivity, argument, state, branch =>
      [{ branch := branch, answer := .refl argument, state := state,
         intents := [if state then 30 else 40] }]

/-- The actual handler realizes every primitive world list exactly, including
untyped arguments; typing preservation is a separate conditional theorem. -/
theorem handler_realizes {n : Nat} (operation : Operation) (argument : Tower.Tm n)
    (state : Bool) (branch : BranchTrace) :
    runWorldsAt (handler operation argument) state branch =
      primitiveWorlds operation argument state branch := by
  cases operation <;> rfl

/-- For every admitted argument, each primitive output has its independently
declared native result type. This checks implementation against declaration. -/
theorem primitive_world_typing {n : Nat} {Γ : Tower.Ctx n}
    (operation : Operation) (argument : Tower.Tm n) (state : Bool) (branch : BranchTrace)
    (world : WorldResult Bool (Tower.Tm n) Nat)
    (admitted : FormationSensitive.Typing Tower.rules Γ argument
      (liftClosed (signature.input operation)))
    (membership : world ∈ primitiveWorlds operation argument state branch) :
    FormationSensitive.Typing Tower.rules Γ world.answer
      (signature.result operation argument) := by
  cases operation with
  | markTrue =>
      simp only [primitiveWorlds, List.mem_singleton] at membership
      subst world
      exact admitted
  | markFalse =>
      simp only [primitiveWorlds, List.mem_singleton] at membership
      subst world
      exact admitted
  | reflexivity =>
      simp only [primitiveWorlds, List.mem_singleton] at membership
      subst world
      exact .reflIntro admitted

/-- Direct source recursion determines the complete ordered worlds. -/
theorem source_worlds (state : Bool) (branch : BranchTrace) :
    Code.worlds primitiveWorlds ids source state branch =
      [{ branch := false :: branch, answer := .pair older (.refl older),
         state := true, intents := [10, 30] },
       { branch := true :: branch, answer := .pair newer (.refl newer),
         state := false, intents := [20, 40] }] := rfl

/-- The separately interpreted program has exactly the source worlds, not
merely the same set of final answers. -/
theorem source_interpretation (state : Bool) (branch : BranchTrace) :
    runWorldsAt (Code.interpret handler ids source) state branch =
      [{ branch := false :: branch, answer := .pair older (.refl older),
         state := true, intents := [10, 30] },
       { branch := true :: branch, answer := .pair newer (.refl newer),
         state := false, intents := [20, 40] }] := by
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact source_worlds state branch

theorem native_pair_answers :
    (runWorlds (Code.interpret handler ids source) false).map WorldResult.answer =
      [.pair (.var 1) (.refl (.var 1)), .pair (.var 0) (.refl (.var 0))] := by
  rw [runWorlds, source_interpretation]
  rfl

/-- Resetting the body to the initial state loses the selected world's
effects even though the native selected value remains available. -/
theorem initial_state_reset_changes_intents :
    (Code.worlds primitiveWorlds ids source false []).map WorldResult.intents ≠
      ((Code.worlds primitiveWorlds ids first false []).flatMap fun prior =>
        (Code.worlds primitiveWorlds (consSub prior.answer ids) body false prior.branch).map
          fun later => prior.intents ++ later.intents) := by decide

/-- These two native result types are syntactically distinct. -/
theorem selected_types_differ :
    inst0 older identityFamily ≠ inst0 newer identityFamily := by decide

/-- The wrong selected index is rejected by the actual native judgment,
including all of its conversion and cumulativity tail rules. -/
theorem wrong_selected_index_not_admitted :
    ¬ FormationSensitive.Typing Tower.rules context (.refl older)
      (signature.result .reflexivity newer) := by
  intro admitted
  exact FormationSensitive.DependentComputation.Examples.wrong_selected_index_not_admitted
    ⟨context_formed, admitted⟩

end ScopedComputation.NativeExamples

#print axioms ScopedComputation.NativeExamples.operation_formation
#print axioms ScopedComputation.NativeExamples.context_formed
#print axioms ScopedComputation.NativeExamples.source_typing
#print axioms ScopedComputation.NativeExamples.source_judgment
#print axioms ScopedComputation.NativeExamples.handler_realizes
#print axioms ScopedComputation.NativeExamples.primitive_world_typing
#print axioms ScopedComputation.NativeExamples.source_worlds
#print axioms ScopedComputation.NativeExamples.source_interpretation
#print axioms ScopedComputation.NativeExamples.native_pair_answers
#print axioms ScopedComputation.NativeExamples.initial_state_reset_changes_intents
#print axioms ScopedComputation.NativeExamples.wrong_selected_index_not_admitted

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
