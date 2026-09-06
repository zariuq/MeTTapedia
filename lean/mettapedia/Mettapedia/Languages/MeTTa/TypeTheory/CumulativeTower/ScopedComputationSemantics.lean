import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputation
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Interpretation of scoped computations in contextual worlds

Scoped source code is interpreted through the existing contextual effect
program. Independently, source recursion defines its ordered world results
from a primitive operation relation presented as world lists. When primitive
handlers realize those lists, the interpretations agree exactly, retaining
states, branch occurrences, multiplicity and deferred intents.

The interpretation commutes with actual native value substitution, including
the lifted substitution beneath both sequence binders. This does not infer a
typing judgment or equate ordinary sequence with a lazy need binder. The
source remains the supported computation fragment, not a full CBPV calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uState uAnswer uIntent

/-- Every execution of the existing well-founded computation syntax retains
at least one world. There is no abort or empty-choice constructor here; native
payloads are returned as data, not normalized by this assertion. -/
theorem runWorldsAt_ne_nil {State : Type uState} {Answer : Type uAnswer}
    {Intent : Type uIntent} (program : Program State Answer Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt program state branch ≠ [] := by
  induction program generalizing state branch with
  | pure answer => exact List.cons_ne_nil _ _
  | choose left right leftIH _ =>
      intro empty
      exact leftIH state (false :: branch) (List.append_eq_nil_iff.mp empty).1
  | read next nextIH => exact nextIH state state branch
  | write newState next nextIH => exact nextIH newState branch
  | intent request next nextIH =>
      intro empty
      exact nextIH state branch (List.map_eq_nil_iff.mp empty)

end Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uState uIntent

variable {Head Operation : Type} {State : Type uState} {Intent : Type uIntent}
  {n m k : Nat}

namespace Code

/-- Interpret existing native payloads using an explicit simultaneous value
environment. Both sequence bodies bind the actual selected answer. -/
def interpret {n : Nat}
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (environment : Sub Head n m) : Code Head Operation n →
      Program State (Tm Head m) Intent
  | .returnValue value => .pure (subst environment value)
  | .sequence first body =>
      (interpret handler environment first).bind fun answer =>
        interpret handler (consSub answer environment) body
  | .sequenceSigma first body =>
      (interpret handler environment first).bind fun answer =>
        Program.map (Tm.pair answer)
          (interpret handler (consSub answer environment) body)
  | .choose left right =>
      .choose (interpret handler environment left) (interpret handler environment right)
  | .call operation argument => handler operation (subst environment argument)

/-- Direct source semantics. No contextual-program interpreter is called in
this definition. Primitive world lists are its only effect-specific input. -/
def worlds {n : Nat}
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (environment : Sub Head n m) : Code Head Operation n → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent)
  | .returnValue value, state, branch =>
      [{ branch := branch, answer := subst environment value, state := state, intents := [] }]
  | .sequence first body, state, branch =>
      (worlds primitive environment first state branch).flatMap fun prior =>
        (worlds primitive (consSub prior.answer environment) body prior.state prior.branch).map
          fun later =>
            { branch := later.branch, answer := later.answer, state := later.state,
              intents := prior.intents ++ later.intents }
  | .sequenceSigma first body, state, branch =>
      (worlds primitive environment first state branch).flatMap fun prior =>
        (worlds primitive (consSub prior.answer environment) body prior.state prior.branch).map
          fun later =>
            { branch := later.branch, answer := .pair prior.answer later.answer,
              state := later.state, intents := prior.intents ++ later.intents }
  | .choose left right, state, branch =>
      worlds primitive environment left state (false :: branch) ++
        worlds primitive environment right state (true :: branch)
  | .call operation argument, state, branch =>
      primitive operation (subst environment argument) state branch

/-- Direct source execution has a result when every primitive call has one.
The conclusion concerns the finite computation fragment, not type formation,
value normalization, a runtime evaluation strategy, or full-CBPV progress. -/
theorem worlds_ne_nil
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (total : ∀ operation argument state branch,
      primitive operation argument state branch ≠ [])
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    worlds primitive environment code state branch ≠ [] := by
  induction code generalizing state branch with
  | returnValue value => exact List.cons_ne_nil _ _
  | sequence first body firstIH bodyIH =>
      intro empty
      obtain ⟨prior, member⟩ := List.exists_mem_of_ne_nil _ (firstIH environment state branch)
      exact bodyIH (consSub prior.answer environment) prior.state prior.branch
        (List.map_eq_nil_iff.mp (List.flatMap_eq_nil_iff.mp empty prior member))
  | sequenceSigma first body firstIH bodyIH =>
      intro empty
      obtain ⟨prior, member⟩ := List.exists_mem_of_ne_nil _ (firstIH environment state branch)
      exact bodyIH (consSub prior.answer environment) prior.state prior.branch
        (List.map_eq_nil_iff.mp (List.flatMap_eq_nil_iff.mp empty prior member))
  | choose left right leftIH _ =>
      intro empty
      exact leftIH environment state (false :: branch) (List.append_eq_nil_iff.mp empty).1
  | call operation argument => exact total operation _ state branch

/-- Exact ordered-list agreement for arbitrary source code follows from the
independently stated primitive handler contract. -/
theorem interpret_worlds
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (realizes : ∀ operation argument state branch,
      runWorldsAt (handler operation argument) state branch =
        primitive operation argument state branch)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (interpret handler environment code) state branch =
      worlds primitive environment code state branch := by
  induction code generalizing state branch with
  | returnValue value => rfl
  | sequence first body firstIH bodyIH =>
      simp only [interpret, worlds,
        Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_bind,
        firstIH, bodyIH]
      rfl
  | sequenceSigma first body firstIH bodyIH =>
      simp only [interpret, worlds,
        Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_bind,
        Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_map,
        firstIH, bodyIH, List.map_map, Function.comp_def,
        Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.prependIntents,
        Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer]
  | choose left right leftIH rightIH =>
      simp only [interpret, worlds, runWorldsAt, leftIH, rightIH]
  | call operation argument => exact realizes operation _ state branch

/-- Realization by this handler language entails the primitive total-results
contract, so its source-world semantics is nonempty as well. -/
theorem worlds_ne_nil_of_realization
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (realizes : ∀ operation argument state branch,
      runWorldsAt (handler operation argument) state branch =
        primitive operation argument state branch)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    worlds primitive environment code state branch ≠ [] := by
  rw [← interpret_worlds handler primitive realizes]
  exact runWorldsAt_ne_nil _ state branch

/-- Opening the newest binder cancels the weakening of all older variables.
This is an equality of the actual native value environments. -/
theorem consSub_liftSub_comp (answer : Tm Head k)
    (later : Sub Head m k) (earlier : Sub Head n m) :
    subComp (consSub answer later) (liftSub earlier) =
      consSub answer (subComp later earlier) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    exact subst_consSub_rename_wk answer later (earlier previous)

/-- Source value substitution commutes with interpretation. The source
substitution is lifted under each computation binder, not replaced by a host
continuation substitution. -/
theorem interpret_substitute
    (handler : Operation → Tm Head k → Program State (Tm Head k) Intent)
    (later : Sub Head m k) (earlier : Sub Head n m) (code : Code Head Operation n) :
    interpret handler later (code.substitute earlier) =
      interpret handler (subComp later earlier) code := by
  induction code generalizing m with
  | returnValue value =>
      simp only [substitute, interpret, subst_subComp]
  | sequence first body firstIH bodyIH =>
      simp only [substitute, interpret, firstIH]
      congr 1
      funext answer
      rw [bodyIH, consSub_liftSub_comp]
  | sequenceSigma first body firstIH bodyIH =>
      simp only [substitute, interpret, firstIH]
      congr 1
      funext answer
      rw [bodyIH, consSub_liftSub_comp]
  | choose left right leftIH rightIH =>
      simp only [substitute, interpret, leftIH, rightIH]
  | call operation argument =>
      simp only [substitute, interpret, subst_subComp]

/-- Opening a source binder is interpreted by extending the current native
environment with the substituted argument. -/
theorem interpret_instantiate
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (environment : Sub Head n m) (argument : Tm Head n)
    (body : Code Head Operation (n + 1)) :
    interpret handler environment (body.instantiate argument) =
      interpret handler (consSub (subst environment argument) environment) body := by
  rw [instantiate, interpret_substitute]
  congr 1
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro previous
    rfl

/-- The return/sequence equation exposes the selected value substitution.
It does not authorize inlining an arbitrary effectful producer. -/
theorem interpret_sequence_return
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (environment : Sub Head n m) (value : Tm Head n)
    (body : Code Head Operation (n + 1)) :
    interpret handler environment (.sequence (.returnValue value) body) =
      interpret handler environment (body.instantiate value) := by
  rw [interpret_instantiate]
  rfl

/-- Every direct source-world result is an actual handler result, and vice
versa; the stronger list equality also retains order and multiplicity. -/
theorem mem_interpret_iff_worlds
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (realizes : ∀ operation argument state branch,
      runWorldsAt (handler operation argument) state branch =
        primitive operation argument state branch)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace)
    (result : WorldResult State (Tm Head m) Intent) :
    result ∈ runWorldsAt (interpret handler environment code) state branch ↔
      result ∈ worlds primitive environment code state branch := by
  rw [interpret_worlds handler primitive realizes]

end Code

namespace SemanticsExamples

def impossibleHandler {n : Nat} : Empty → Tm Nat n → Program Unit (Tm Nat n) Unit :=
  fun operation => nomatch operation

/-- The sequence binds a new value, but its body refers to the older free
variable. Native lifting keeps these two positions separate. -/
def outerVariable : Code Nat Empty 1 :=
  .sequence (.returnValue (.head 7)) (.returnValue (.var 1))

def closing : Sub Nat 1 0 := fun _ => .head 42

theorem older_variable_not_captured :
    runWorlds (Code.interpret impossibleHandler ids (outerVariable.substitute closing)) () =
      [{ branch := [], answer := .head 42, state := (), intents := [] }] := by
  rfl

/-- Accidentally using the new binder instead changes the exact result. -/
theorem captured_variable_changes_answer :
    (runWorlds (Code.interpret impossibleHandler ids (outerVariable.substitute closing)) ()).map
        WorldResult.answer ≠
      (runWorlds (Code.interpret impossibleHandler ids
        (.sequence (.returnValue (.head 7)) (.returnValue (.var 0)) : Code Nat Empty 0)) ()).map
          WorldResult.answer := by
  decide

/-- A finite operation with two independently specified contextual outcomes. -/
def choiceHandler : Unit → Tm Nat 0 → Program Unit (Tm Nat 0) Unit :=
  fun _ _ => .choose (.pure (.head 1)) (.pure (.head 2))

def choiceWorlds : Unit → Tm Nat 0 → Unit → BranchTrace →
    List (WorldResult Unit (Tm Nat 0) Unit) :=
  fun _ _ state branch =>
    [{ branch := false :: branch, answer := .head 1, state := state, intents := [] },
     { branch := true :: branch, answer := .head 2, state := state, intents := [] }]

theorem choiceHandler_realizes : ∀ operation argument state branch,
    runWorldsAt (choiceHandler operation argument) state branch =
      choiceWorlds operation argument state branch := by
  intros
  rfl

/-- Returning the selected value twice is one call, not two sampled calls. -/
def reuseChosen : Code Nat Unit 0 :=
  .sequence (.call () (.head 0)) (.returnValue (.pair (.var 0) (.var 0)))

def repeatCall : Code Nat Unit 0 :=
  .sequence (.call () (.head 0))
    (.sequence (.call () (.head 0)) (.returnValue (.pair (.var 1) (.var 0))))

theorem reuseChosen_answers :
    (Code.worlds choiceWorlds ids reuseChosen () []).map WorldResult.answer =
      [.pair (.head 1) (.head 1), .pair (.head 2) (.head 2)] := by
  rfl

theorem repeatCall_answers :
    (Code.worlds choiceWorlds ids repeatCall () []).map WorldResult.answer =
      [.pair (.head 1) (.head 1), .pair (.head 1) (.head 2),
       .pair (.head 2) (.head 1), .pair (.head 2) (.head 2)] := by
  rfl

/-- The independent source observations distinguish reusing a selected value
from repeating its effectful producer; exact interpretation transfers this
distinction to the existing handler. -/
theorem repeated_choice_changes_interpretation :
    (runWorlds (Code.interpret choiceHandler ids reuseChosen) ()).map WorldResult.answer ≠
      (runWorlds (Code.interpret choiceHandler ids repeatCall) ()).map WorldResult.answer := by
  unfold runWorlds
  rw [Code.interpret_worlds choiceHandler choiceWorlds choiceHandler_realizes,
    Code.interpret_worlds choiceHandler choiceWorlds choiceHandler_realizes,
    reuseChosen_answers, repeatCall_answers]
  decide

/-- The nonempty primitive hypothesis cannot be dropped: a primitive with
no results makes an actual source call have no direct source worlds. -/
theorem empty_primitive_has_no_worlds :
    Code.worlds (fun (_ : Unit) (_ : Tm Nat 0) (_ : Unit) (_ : BranchTrace) =>
      ([] : List (WorldResult Unit (Tm Nat 0) Unit))) ids
      (.call () (.head 0) : Code Nat Unit 0) () [] = [] := by
  rfl

/-- An aborting primitive cannot be implemented by the current total-results
handler syntax. Adding failure requires a separately justified extension. -/
theorem empty_primitive_has_no_handler :
    ¬ ∃ handler : Unit → Tm Nat 0 → Program Unit (Tm Nat 0) Unit,
      ∀ operation argument state branch,
        runWorldsAt (handler operation argument) state branch = [] := by
  rintro ⟨handler, empty⟩
  exact runWorldsAt_ne_nil (handler () (.head 0)) () [] (empty () (.head 0) () [])

end SemanticsExamples

#print axioms Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.runWorldsAt_ne_nil
#print axioms Code.worlds_ne_nil
#print axioms Code.worlds_ne_nil_of_realization
#print axioms Code.interpret_worlds
#print axioms Code.consSub_liftSub_comp
#print axioms Code.interpret_substitute
#print axioms Code.interpret_instantiate
#print axioms Code.interpret_sequence_return
#print axioms Code.mem_interpret_iff_worlds
#print axioms SemanticsExamples.older_variable_not_captured
#print axioms SemanticsExamples.captured_variable_changes_answer
#print axioms SemanticsExamples.choiceHandler_realizes
#print axioms SemanticsExamples.repeated_choice_changes_interpretation
#print axioms SemanticsExamples.empty_primitive_has_no_worlds
#print axioms SemanticsExamples.empty_primitive_has_no_handler

end ScopedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
