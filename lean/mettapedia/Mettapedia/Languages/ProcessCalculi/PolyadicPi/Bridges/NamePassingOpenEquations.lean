import Mettapedia.Languages.LambdaCalculus.NamePassingPresentationEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenReduction

/-!
# Open application scope equations and active communications

Both application scope laws are implemented by the target's actual scope
extrusion and exchange. Independently supplied program bodies commute with
the exchange through the complete target substitution theorem. The resulting
static derivations and active source edge occurrences retain their supplied
translated endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

def listener {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (name : Name Δ) : Proc Δ :=
  inp1 name (interpret value (environment.substitute weakening) (.var .zero))

def server {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (name : Name Δ) : Proc Δ :=
  rep (listener value environment name)

theorem listener_target_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ)
    (name : Name Δ) (substitution : Sub sig Δ Θ) :
    Mettapedia.OSLF.Binding.bind substitution (listener value environment name) =
      listener value (environment.substitute substitution) (Mettapedia.OSLF.Binding.bind substitution name) := by
  change inp1 (Mettapedia.OSLF.Binding.bind substitution name)
    (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm])
      (interpret value (environment.substitute weakening) (.var .zero))) = _
  rw [interpret_target_substitution, Environment.weaken_substitute]
  rfl

theorem server_target_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ)
    (name : Name Δ) (substitution : Sub sig Δ Θ) :
    Mettapedia.OSLF.Binding.bind substitution (server value environment name) =
      server value (environment.substitute substitution) (Mettapedia.OSLF.Binding.bind substitution name) := by
  exact congrArg rep (listener_target_substitution value environment name substitution)

theorem listener_weakening {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (name : Name Δ) :
    listener value (environment.substitute weakening) (weaken name) =
      weaken (listener value environment name) := by
  have comparison := listener_target_substitution value environment name weakening
  have nameComparison : Mettapedia.OSLF.Binding.bind weakening name = weaken name :=
    bind_var_eq_rename (fun _ position => .succ position) name
  have processComparison : Mettapedia.OSLF.Binding.bind weakening (listener value environment name) =
      weaken (listener value environment name) := bind_var_eq_rename (fun _ position => .succ position) _
  rw [nameComparison, processComparison] at comparison
  exact comparison.symm

theorem server_weakening {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) (name : Name Δ) :
    server value (environment.substitute weakening) (weaken name) =
      weaken (server value environment name) := by
  have comparison := server_target_substitution value environment name weakening
  have nameComparison : Mettapedia.OSLF.Binding.bind weakening name = weaken name :=
    bind_var_eq_rename (fun _ position => .succ position) name
  have processComparison : Mettapedia.OSLF.Binding.bind weakening (server value environment name) =
      weaken (server value environment name) := bind_var_eq_rename (fun _ position => .succ position) _
  rw [nameComparison, processComparison] at comparison
  exact comparison.symm

theorem Environment.definition_exchange {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) :
    (environment.substitute weakening).lift.substitute (fun _ position => .var (swapRen _ position)) =
      environment.lift.substitute weakening := by
  apply Environment.ext
  · funext name
    cases name with
    | zero => rfl
    | succ name =>
        simp only [substitute, lift, weaken, bind_rename, bind_comp]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.name name))
        funext s position
        rfl
  · funext term
    cases term with
    | succ term =>
        simp only [substitute, lift, bind_comp]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.program term))
        funext s position
        cases position with
        | zero => rfl
        | succ position => rfl

theorem Environment.double_weakening_exchange {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (environment : Environment Γ Δ) :
    ((environment.substitute weakening).substitute weakening).substitute
        (fun _ position => .var (swapRen _ position)) =
      (environment.substitute weakening).substitute weakening := by
  apply Environment.ext
  · funext name
    simp only [substitute, bind_comp]
    apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.name name))
    funext s position
    rfl
  · funext term
    simp only [substitute, bind_comp]
    apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned (environment.program term))
    funext s position
    cases position with
    | zero => rfl
    | succ position => rfl

theorem definition_body_exchange {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ)) (environment : Environment Γ Δ) :
    rename swapRen (interpret body (environment.substitute weakening).lift (.var (.succ .zero))) =
      interpret body (environment.lift.substitute weakening) (.var .zero) := by
  rw [← bind_var_eq_rename swapRen, interpret_target_substitution, Environment.definition_exchange]
  rfl

theorem definition_server_exchange {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (environment : Environment Γ Δ) :
    rename swapRen (server value ((environment.substitute weakening).substitute weakening) (.var .zero)) =
      weaken (server value (environment.substitute weakening) (.var .zero)) := by
  rw [← bind_var_eq_rename swapRen, server_target_substitution, Environment.double_weakening_exchange]
  exact server_weakening value (environment.substitute weakening) (.var .zero)

theorem double_weakening_exchange {Δ : Ctx sig} {s : sig.Srt} (term : Term sig Δ s) :
    rename swapRen (weaken (weaken term)) = weaken (weaken term) := by
  simp only [weaken, rename_comp]
  apply congrArg (fun assigned => rename assigned term)
  funext s position
  rfl

private theorem frame_exchange {Δ : Ctx sig} (body declaration call : Proc Δ) :
    StructuralEq (par (par body declaration) call) (par (par body call) declaration) :=
  .trans (.parAssoc _ _ _) (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))

theorem application_carrier {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (name : NamePassing.Presentation.Name Γ) (value body : NamePassing.Presentation.Program Γ)
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    StructuralEq (interpret (NamePassing.Presentation.application
      (NamePassing.Presentation.carrier name value body) argument) environment result)
      (interpret (NamePassing.Presentation.carrier name value
        (NamePassing.Presentation.application body argument)) environment result) := by
  simp only [NamePassing.Presentation.application, NamePassing.Presentation.carrier, interpret]
  change StructuralEq (nu (par (par (interpret body (environment.substitute weakening) (.var .zero))
    (listener value (environment.substitute weakening) (interpretName name (environment.substitute weakening))))
    (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result))))
    (par (nu (par (interpret body (environment.substitute weakening) (.var .zero))
      (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result))))
      (listener value environment (interpretName name environment)))
  rw [← interpretName_substitute]
  have nameComparison : Mettapedia.OSLF.Binding.bind weakening (interpretName name environment) =
      weaken (interpretName name environment) := bind_var_eq_rename (fun _ position => .succ position) _
  rw [nameComparison, listener_weakening]
  exact .trans (.nu (frame_exchange _ _ _)) (.symm (.nuPar _ _))

theorem application_definition {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (value : NamePassing.Presentation.Program Γ) (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    StructuralEq (interpret (NamePassing.Presentation.application
      (NamePassing.Presentation.definition value body) argument) environment result)
      (interpret (NamePassing.Presentation.definition value
        (NamePassing.Presentation.application body (weaken argument))) environment result) := by
  let inside : Proc (.nm :: .nm :: Δ) :=
    par (interpret body (environment.substitute weakening).lift (.var (.succ .zero)))
      (server value ((environment.substitute weakening).substitute weakening) (.var .zero))
  let call : Proc (.nm :: Δ) :=
    out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result)
  let received : Proc (.nm :: .nm :: Δ) := interpret body (environment.lift.substitute weakening) (.var .zero)
  let continuation : Proc (.nm :: .nm :: Δ) :=
    out2 (.var .zero) (weaken (weaken (interpretName argument environment))) (weaken (weaken result))
  let retained : Proc (.nm :: Δ) := server value (environment.substitute weakening) (.var .zero)
  have aligned : rename swapRen (par inside (weaken call)) =
      par (par received (weaken retained)) continuation := by
    dsimp only [inside, received, retained, continuation, call]
    rw [rename_par, rename_par, definition_body_exchange, definition_server_exchange]
    change par _ (out2 (.var .zero)
      (rename swapRen (weaken (weaken (interpretName argument environment))))
      (rename swapRen (weaken (weaken result)))) = _
    rw [double_weakening_exchange, double_weakening_exchange]
  simp only [NamePassing.Presentation.application, NamePassing.Presentation.definition, interpret]
  have bodyArgument : interpretName (weaken argument) environment.lift =
      weaken (interpretName argument environment) := by
    rw [weaken, interpretName_source_rename, Environment.forget_new_name]
    exact (interpretName_substitute argument environment weakening).symm.trans
      (bind_var_eq_rename (fun _ position => .succ position) _)
  rw [bodyArgument]
  change StructuralEq (nu (par (nu inside) call)) (nu (par (nu (par received continuation)) retained))
  apply StructuralEq.trans (.nu (.nuPar inside call))
  apply StructuralEq.trans (.nuSwap (par inside (weaken call)))
  rw [aligned]
  exact .trans (.nu (.nu (frame_exchange _ _ _))) (.nu (.symm (.nuPar _ _)))

/-- Every supplied static derivation has an actual target structural
comparison at the supplied full name/program environment. -/
theorem static_preserved {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    {source target : NamePassing.Presentation.Program Γ}
    (equal : NamePassing.Presentation.StaticEq source target)
    (environment : Environment Γ Δ) (result : Name Δ) :
    StructuralEq (interpret source environment result) (interpret target environment result) := by
  induction equal generalizing Δ with
  | refl => exact .refl _
  | symm _ inductionHypothesis => exact .symm (inductionHypothesis environment result)
  | trans _ _ firstHypothesis secondHypothesis =>
      exact .trans (firstHypothesis environment result) (secondHypothesis environment result)
  | appDefinition value body argument => exact application_definition value body argument environment result
  | appCarrier name value body argument => exact application_carrier name value body argument environment result
  | abstraction _ inductionHypothesis =>
      simp only [NamePassing.Presentation.abstraction, interpret]
      exact .inp2 _ (inductionHypothesis (environment.substitute weakening).lift (.var (.succ .zero)))
  | application argument _ inductionHypothesis =>
      simp only [NamePassing.Presentation.application, interpret]
      exact .nu (.par (inductionHypothesis (environment.substitute weakening) (.var .zero)) (.refl _))
  | definition _ _ valueHypothesis bodyHypothesis =>
      simp only [NamePassing.Presentation.definition, interpret]
      exact .nu (.par (bodyHypothesis environment.lift (weaken result))
        (.rep (.inp1 _ (valueHypothesis ((environment.substitute weakening).substitute weakening) (.var .zero)))))
  | carrier name _ _ valueHypothesis bodyHypothesis =>
      simp only [NamePassing.Presentation.carrier, interpret]
      exact .par (bodyHypothesis environment result)
        (.inp1 _ (valueHypothesis (environment.substitute weakening) (.var .zero)))

private theorem modulo_parallel {Δ : Ctx sig} {first second : Proc Δ}
    (frame : Proc Δ) (edge : StepModulo first second) : StepModulo (par first frame) (par second frame) := by
  obtain ⟨before, after, sourceEqual, firing, targetEqual⟩ := edge
  exact ⟨par before frame, par after frame, .par sourceEqual (.refl _), .parL frame firing,
    .par targetEqual (.refl _)⟩

private theorem modulo_restriction {Δ : Ctx sig} {first second : Proc (.nm :: Δ)}
    (edge : StepModulo first second) : StepModulo (nu first) (nu second) := by
  obtain ⟨before, after, sourceEqual, firing, targetEqual⟩ := edge
  exact ⟨nu before, nu after, .nu sourceEqual, .nu firing, .nu targetEqual⟩

/-- Every supplied active edge occurrence is preserved. Suspended source
positions are interpreted but are not declared active by this relation. -/
theorem active_preserved {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    {source target : NamePassing.Presentation.Program Γ}
    (edge : NamePassing.Presentation.ActiveEdge source target)
    (environment : Environment Γ Δ) (result : Name Δ) :
    StepModulo (interpret source environment result) (interpret target environment result) := by
  induction edge generalizing Δ with
  | root edge => exact rootEdge_preserved edge environment result
  | application argument edge inductionHypothesis =>
      simp only [NamePassing.Presentation.application, interpret]
      exact modulo_restriction (modulo_parallel _ (inductionHypothesis (environment.substitute weakening) (.var .zero)))
  | definition value edge inductionHypothesis =>
      simp only [NamePassing.Presentation.definition, interpret]
      exact modulo_restriction (modulo_parallel _ (inductionHypothesis environment.lift (weaken result)))
  | carrier name value edge inductionHypothesis =>
      simp only [NamePassing.Presentation.carrier, interpret]
      exact modulo_parallel _ (inductionHypothesis environment result)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation
