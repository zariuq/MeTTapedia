import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedTypingExamples

/-!
# Executed first-class functions returning native identity evidence

A native-dependent computation function is thunked, passed through a source
value abstraction, forced, and applied to a native argument. Exact candidate
machine execution determines its returned term. Separately, independent native
argument admission licenses that term at the argument-indexed identity type.
The source template has one native variable; its lexical environment carries
an arbitrary native argument into an arbitrary target native context.

These are particular source programs with symbolic native arguments. They do
not assert whole-runtime subject reduction, termination of arbitrary source,
or native admission from raw execution alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedDependentExecution

open PrimeNeedReference PolarizedNeed PolarizedNeedMachine

variable {Operation StableFault NativeFault : Type} {m : Nat}

def initial (argument : Tower.Tm m) (code : Computation Tower.Head Operation Nat 1 0 0) :
    NeedMachine Tower.Head Operation Nat StableFault NativeFault m where
  world := ⟨0, [], .empty, .empty, 0, 0⟩
  control := .run (.evaluate
    ⟨1, 0, 0, code, Fin.cases argument Fin.elim0, Fin.elim0, Fin.elim0⟩ .done) []

/-- The function and higher-order consumer are independently authored source
definitions from the source-admission examples. -/
def passedApplication (argument : Tower.Tm m) : Computation Tower.Head Operation Nat m 0 0 :=
  .nativeApply Examples.passedFunction argument

theorem passed_application_typed
    {signature : ScopedComputation.OperationSignature Tower.Head Operation}
    {Γ : Tower.Ctx m} {argument : Tower.Tm m}
    (admitted : FormationSensitive.Typing Tower.rules Γ argument Examples.ground) :
    ComputationTyping Tower.rules signature Γ Fin.elim0 Fin.elim0 (passedApplication argument)
      (.returns (.native (.id Examples.ground argument argument))) :=
  Examples.passed_function_application_typed admitted

def sourceContext : Tower.Ctx 1 := .snoc .nil Examples.ground

theorem source_context_formed : FormationSensitive.ContextFormation Tower.rules sourceContext :=
  .snoc .nil (.headType .legacyGround) (.sort Tower.zero)

theorem template_typed
    (signature : ScopedComputation.OperationSignature Tower.Head Operation) :
    ComputationTyping Tower.rules signature sourceContext Fin.elim0 Fin.elim0
      (passedApplication (.var 0))
      (.returns (.native (.id Examples.ground (.var 0) (.var 0)))) :=
  passed_application_typed (.var 0)

/-- Loading the parameter is independently a typed native substitution. -/
theorem parameter_environment_typed {Γ : Tower.Ctx m} {argument : Tower.Tm m}
    (admitted : FormationSensitive.Typing Tower.rules Γ argument Examples.ground) :
    FormationSensitive.CtxMor Tower.rules sourceContext Γ (Fin.cases argument Fin.elim0) := by
  intro index
  refine Fin.cases ?_ (fun index => Fin.elim0 index) index
  exact admitted

/-- Explicit intermediate controls are a finite execution witness. They are
not a replacement evaluator; each edge is checked against the actual step. -/
def traceControl (argument : Tower.Tm m) : Fin 8 →
    Control (Local Tower.Head Operation Nat StableFault NativeFault m)
      (Resume Tower.Head Operation Nat m) (Answer Tower.Head Operation Nat m)
      StableFault (Fault NativeFault)
  | 0 => .run (.evaluate
      ⟨1, 0, 0, passedApplication (.var 0), Fin.cases argument Fin.elim0, Fin.elim0, Fin.elim0⟩ .done) []
  | 1 => .run (.evaluate
      ⟨1, 0, 0, Examples.passedFunction, Fin.cases argument Fin.elim0, Fin.elim0, Fin.elim0⟩
      (.nativeApply argument .done)) []
  | 2 => .run (.evaluate
      ⟨1, 0, 0, forceArgument, Fin.cases argument Fin.elim0, Fin.elim0, Fin.elim0⟩
      (.valueApply (.thunk Examples.reflexiveFunction (Fin.cases argument Fin.elim0) Fin.elim0 Fin.elim0)
        (.nativeApply argument .done))) []
  | 3 => .run (.evaluate
      ⟨1, 1, 0, .forceThunk (.variable 0), Fin.cases argument Fin.elim0,
        Fin.cases (.thunk Examples.reflexiveFunction (Fin.cases argument Fin.elim0) Fin.elim0 Fin.elim0)
          Fin.elim0, Fin.elim0⟩ (.nativeApply argument .done)) []
  | 4 => .run (.evaluate
      ⟨1, 0, 0, Examples.reflexiveFunction, Fin.cases argument Fin.elim0, Fin.elim0, Fin.elim0⟩
      (.nativeApply argument .done)) []
  | 5 => .run (.evaluate
      ⟨2, 0, 0, .returnValue (.native (.refl (.var 0))),
        Fin.cases argument (Fin.cases argument Fin.elim0), Fin.elim0, Fin.elim0⟩ .done) []
  | 6 => .returned (.value (.returned (.native (.refl argument)))) []
  | 7 => .halted (.value (.returned (.native (.refl argument))))

def traceMachine (argument : Tower.Tm m) (index : Fin 8) :
    NeedMachine Tower.Head Operation Nat StableFault NativeFault m where
  world := ⟨0, [], .empty, .empty, 0, 0⟩
  control := traceControl argument index
  work := ⟨index.val, 0, 0, 0, 0⟩

theorem trace_steps
    (primitive : Operation → Tower.Tm m → Produced (Tower.Tm m) StableFault NativeFault)
    (argument : Tower.Tm m) (index : Fin 7) :
    PrimeNeedLocalSteps.step (extension primitive) (traceMachine argument index.castSucc) =
      [traceMachine argument index.succ] := by
  fin_cases index <;> rfl

private theorem frontier_one
    (primitive : Operation → Tower.Tm m → Produced (Tower.Tm m) StableFault NativeFault)
    (fuel : Nat) (machine next : NeedMachine Tower.Head Operation Nat StableFault NativeFault m)
    (live : isHalted machine = false)
    (stepped : PrimeNeedLocalSteps.step (extension primitive) machine = [next]) :
    PrimeNeedLocalSteps.runFrontier (extension primitive) (fuel + 1) [machine] =
      PrimeNeedLocalSteps.runFrontier (extension primitive) fuel [next] := by
  simp only [PrimeNeedLocalSteps.runFrontier, List.all_cons, List.all_nil, live,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, PrimeNeedLocalSteps.advance, stepped]

/-- Seven actual transitions include value application, ordinary thunk force,
native application, and the unchanged return protocol. No world is captured. -/
theorem passed_frontier
    (primitive : Operation → Tower.Tm m → Produced (Tower.Tm m) StableFault NativeFault)
    (argument : Tower.Tm m) :
    PrimeNeedLocalSteps.runFrontier (extension primitive) 7 [initial argument (passedApplication (.var 0))] =
      [⟨⟨0, [], .empty, .empty, 0, 0⟩,
        .halted (.value (.returned (.native (.refl argument)))), ⟨7, 0, 0, 0, 0⟩⟩] := by
  change PrimeNeedLocalSteps.runFrontier (extension primitive) 7 [traceMachine argument 0] = _
  calc
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 6 [traceMachine argument 1] :=
      frontier_one primitive 6 _ _ rfl (trace_steps primitive argument 0)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 5 [traceMachine argument 2] :=
      frontier_one primitive 5 _ _ rfl (trace_steps primitive argument 1)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 4 [traceMachine argument 3] :=
      frontier_one primitive 4 _ _ rfl (trace_steps primitive argument 2)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 3 [traceMachine argument 4] :=
      frontier_one primitive 3 _ _ rfl (trace_steps primitive argument 3)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 2 [traceMachine argument 5] :=
      frontier_one primitive 2 _ _ rfl (trace_steps primitive argument 4)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 1 [traceMachine argument 6] :=
      frontier_one primitive 1 _ _ rfl (trace_steps primitive argument 5)
    _ = PrimeNeedLocalSteps.runFrontier (extension primitive) 0 [traceMachine argument 7] :=
      frontier_one primitive 0 _ _ rfl (trace_steps primitive argument 6)
    _ = _ := rfl

theorem passed_answers
    (primitive : Operation → Tower.Tm m → Produced (Tower.Tm m) StableFault NativeFault)
    (argument : Tower.Tm m) :
    PrimeNeedLocalSteps.answers (extension primitive) 7 (initial argument (passedApplication (.var 0))) =
      [.value (.returned (.native (.refl argument)))] := by
  unfold PrimeNeedLocalSteps.answers
  rw [passed_frontier]
  rfl

/-- Successful source execution identifies the returned syntax; independently
admitted input supplies its native identity proof. -/
theorem passed_result_judgment
    (primitive : Operation → Tower.Tm m → Produced (Tower.Tm m) StableFault NativeFault)
    {Γ : Tower.Ctx m} {argument result : Tower.Tm m}
    (admitted : FormationSensitive.Judgment Tower.rules Γ argument Examples.ground)
    (returned : .value (.returned (.native result)) ∈
      PrimeNeedLocalSteps.answers (extension primitive) 7 (initial argument (passedApplication (.var 0)))) :
    FormationSensitive.Judgment Tower.rules Γ result (.id Examples.ground argument argument) := by
  rw [passed_answers, List.mem_singleton] at returned
  have same : result = .refl argument := by cases returned; rfl
  subst result
  have template : FormationSensitive.Judgment Tower.rules sourceContext (.refl (.var 0))
      (.id Examples.ground (.var 0) (.var 0)) :=
    ⟨source_context_formed, .reflIntro (.var 0)⟩
  exact template.substitute admitted.context (parameter_environment_typed admitted.typing)

theorem wrong_selected_result_not_admitted :
    ¬ FormationSensitive.Judgment Tower.rules Examples.context (.refl Examples.older)
      (.id Examples.ground Examples.newer Examples.newer) := by
  intro admitted
  exact ScopedComputation.NativeExamples.wrong_selected_index_not_admitted admitted.typing

#print axioms passed_application_typed
#print axioms template_typed
#print axioms parameter_environment_typed
#print axioms trace_steps
#print axioms passed_frontier
#print axioms passed_answers
#print axioms passed_result_judgment
#print axioms wrong_selected_result_not_admitted

end PolarizedNeedDependentExecution
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
