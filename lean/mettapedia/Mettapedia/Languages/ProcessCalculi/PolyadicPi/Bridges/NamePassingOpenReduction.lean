import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenSubstitution

/-!
# Root rewrites of the open name-passing presentation

The displayed beta and fetch edges retain arbitrary supplied term holes.
Their interpreted endpoints are the actual unary or binary communication
endpoints, with the fresh private channel removed by structural congruence.
The argument and return binders are opened in their distinct positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

/-- Insert an independently supplied source name without changing any old
program's own return binder. -/
def Environment.instantiate {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) (argument : Name Δ) : Environment (.nm :: Γ) Δ where
  name := fun name => match name with
    | .zero => argument
    | .succ old => environment.name old
  program := fun term => match term with
    | .succ old => environment.program old

theorem program_return_weakening {Δ : Ctx sig} (program : Proc (.nm :: Δ)) :
    inst (Mettapedia.OSLF.Binding.bind (liftSub weakening [.nm]) program) (.var .zero) = program := by
  simp only [inst, bind_comp]
  have identity : (fun s position => Mettapedia.OSLF.Binding.bind (extend (.var .zero))
      (liftSub weakening [.nm] s position)) =
      (fun s position => (Term.var position : Term sig (.nm :: Δ) s)) := by
    funext s position
    cases position with
    | zero => rfl
    | succ position => rfl
  rw [identity]
  exact bind_id program

theorem Environment.sourceSubstitute_identity {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) :
    environment.sourceSubstitute (fun _ position => .var position) = environment := by
  apply Environment.ext
  · rfl
  · funext term
    simp only [sourceSubstitute, interpret, substitute]
    exact program_return_weakening _

theorem Environment.sourceSubstitute_composition
    {Γ Ω Ξ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Ξ Δ)
    (first : Sub NamePassing.Presentation.signature Γ Ω)
    (second : Sub NamePassing.Presentation.signature Ω Ξ) :
    (environment.sourceSubstitute second).sourceSubstitute first =
      environment.sourceSubstitute (fun s position => Mettapedia.OSLF.Binding.bind second (first s position)) := by
  apply Environment.ext
  · funext name
    exact (interpretName_source_substitution (first _ name) second environment).symm
  · funext term
    simp only [sourceSubstitute]
    rw [interpret_source_substitution, ← Environment.sourceSubstitute_target]
    rfl

theorem Environment.sourceSubstitute_extend {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) (argument : NamePassing.Presentation.Name Γ) :
    environment.sourceSubstitute (extend argument) = environment.instantiate (interpretName argument environment) := by
  apply Environment.ext
  · funext name
    cases name with
    | zero => rfl
    | succ name => rfl
  · funext term
    cases term with
    | succ term =>
        simp only [sourceSubstitute, extend, interpret, substitute, instantiate]
        exact program_return_weakening _

theorem interpret_instantiate {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    interpret (inst body argument) environment result =
      interpret body (environment.instantiate (interpretName argument environment)) result := by
  rw [inst, interpret_source_substitution, Environment.sourceSubstitute_extend]

/-- Both received names are opened, and the old free environment keeps the
single unused private call name. The complete program bodies retain their
separate distinguished return binder. -/
theorem Environment.binary_open {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) (argument result : Name Δ) :
    ((environment.substitute weakening).substitute weakening).lift.substitute
        (pairSub (weaken argument) (weaken result)) =
      (environment.instantiate argument).substitute weakening := by
  apply Environment.ext
  · funext name
    cases name with
    | zero =>
        change weaken argument = Mettapedia.OSLF.Binding.bind weakening argument
        exact (bind_var_eq_rename (fun _ position => .succ position) _).symm
    | succ name =>
        change Mettapedia.OSLF.Binding.bind (pairSub (weaken argument) (weaken result))
          (weaken (Mettapedia.OSLF.Binding.bind weakening
            (Mettapedia.OSLF.Binding.bind weakening (environment.name name)))) =
          Mettapedia.OSLF.Binding.bind weakening (environment.name name)
        simp only [weaken, bind_rename, bind_comp]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.name name))
        funext s position
        rfl
  · funext term
    cases term with
    | succ term =>
        simp only [substitute, lift, instantiate, bind_comp]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.program term))
        funext s position
        cases position with
        | zero => rfl
        | succ position => rfl

theorem beta_endpoint {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    openPair (interpret body ((environment.substitute weakening).substitute weakening).lift (.var (.succ .zero)))
        (weaken (interpretName argument environment)) (weaken result) =
      weaken (interpret (inst body argument) environment result) := by
  rw [openPair, interpret_target_substitution, Environment.binary_open]
  change interpret body ((environment.instantiate (interpretName argument environment)).substitute weakening)
    (weaken result) = _
  rw [interpret_instantiate]
  have comparison := interpret_target_substitution body
    (environment.instantiate (interpretName argument environment)) result weakening
  have returnName : Mettapedia.OSLF.Binding.bind weakening result = weaken result :=
    bind_var_eq_rename (fun _ position => .succ position) result
  have resultProgram : Mettapedia.OSLF.Binding.bind weakening
      (interpret body (environment.instantiate (interpretName argument environment)) result) =
      weaken (interpret body (environment.instantiate (interpretName argument environment)) result) :=
    bind_var_eq_rename (fun _ position => .succ position) _
  rw [returnName, resultProgram] at comparison
  exact comparison.symm

theorem fetch_preserved {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (name : NamePassing.Presentation.Name Γ) (value : NamePassing.Presentation.Program Γ)
    (environment : Environment Γ Δ) (result : Name Δ) :
    Step (interpret (NamePassing.Presentation.carrier name value (NamePassing.Presentation.reference name))
        environment result) (interpret value environment result) := by
  simp only [NamePassing.Presentation.carrier, NamePassing.Presentation.reference, interpret]
  have firing := Step.comm1 (interpretName name environment) result
    (interpret value (environment.substitute weakening) (.var .zero))
  rw [interpret_open_result] at firing
  exact firing

theorem beta_preserved {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    StepModulo (interpret (NamePassing.Presentation.application
        (NamePassing.Presentation.abstraction body) argument) environment result)
      (interpret (inst body argument) environment result) := by
  let received := interpret body ((environment.substitute weakening).substitute weakening).lift (.var (.succ .zero))
  let input := inp2 (.var .zero) received
  let output := out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result)
  refine ⟨nu (par output input), nu (weaken (interpret (inst body argument) environment result)),
    ?_, ?_, StructuralEq.nuUnused _⟩
  · simp only [NamePassing.Presentation.application, NamePassing.Presentation.abstraction, interpret]
    change StructuralEq (nu (par input output)) (nu (par output input))
    exact StructuralEq.nu (StructuralEq.parComm input output)
  · apply Step.nu
    have firing := Step.comm2 (.var .zero) (weaken (interpretName argument environment)) (weaken result) received
    rw [show received = interpret body ((environment.substitute weakening).substitute weakening).lift
      (.var (.succ .zero)) from rfl, beta_endpoint] at firing
    exact firing

/-- Every actual independently authored root edge of the open source has a
communication at its supplied translated target. -/
theorem rootEdge_preserved {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    {source target : NamePassing.Presentation.Program Γ}
    (edge : NamePassing.Presentation.RootEdge source target)
    (environment : Environment Γ Δ) (result : Name Δ) :
    StepModulo (interpret source environment result) (interpret target environment result) := by
  cases edge with
  | beta body argument => exact beta_preserved body argument environment result
  | fetch name => exact (fetch_preserved name target environment result).toModulo

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation
