import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironment
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

/-!
# Persistent name-passing environment compilation

The source lookup is independently specified by its selected active occurrence.
The target retains the actual replicated server, and each source lookup uses
one unary communication. Parallel reassociation, replication unfolding and
scope extrusion are structural administration. In particular, a lookup below
an application's private call channel can communicate with an enclosing
definition without counting extrusion as another communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

/-- The one-shot target declaration at its actual reference channel. -/
def listener {Γ Δ : Ctx sig} (value : Expr Γ) (ρ : Ren sig Γ Δ)
    (channel : Var Δ .nm) : Proc Δ :=
  inp1 (.var channel) (compile value (push ρ) .zero)

/-- Replication retains the declaration for subsequent fetches. -/
def server {Γ Δ : Ctx sig} (value : Expr Γ) (ρ : Ren sig Γ Δ)
    (channel : Var Δ .nm) : Proc Δ := rep (listener value ρ channel)

theorem listener_target_rename {Γ Δ Θ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (τ : Ren sig Δ Θ) (channel : Var Δ .nm) :
    rename τ (listener value ρ channel) =
      listener value (fun s x => τ s (ρ s x)) (τ _ channel) := by
  simp only [listener, rename_inp1, rename, compile_target_rename, liftRen]
  rfl

theorem listener_source_rename {Γ Δ Θ : Ctx sig} (value : Expr Γ)
    (σ : Ren sig Γ Δ) (ρ : Ren sig Δ Θ) (channel : Var Θ .nm) :
    listener (NamePassing.rename σ value) ρ channel =
      listener value (fun s x => ρ s (σ s x)) channel := by
  simp only [listener, compile_source_rename, push]
  rfl

theorem listener_weaken {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel : Var Δ .nm) :
    weaken (listener value ρ channel) = listener value (push ρ) (.succ channel) :=
  listener_target_rename value ρ (fun _ x => .succ x) channel

theorem listener_under_definition {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel : Var Δ .nm) :
    listener (NamePassing.weaken value) (liftRen ρ [.nm]) (.succ channel) =
      weaken (listener value ρ channel) := by
  unfold NamePassing.weaken
  rw [listener_source_rename, listener_weaken]
  rfl

theorem server_target_rename {Γ Δ Θ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (τ : Ren sig Δ Θ) (channel : Var Δ .nm) :
    rename τ (server value ρ channel) =
      server value (fun s x => τ s (ρ s x)) (τ _ channel) := by
  simp only [server, rename_rep, listener_target_rename]

theorem server_source_rename {Γ Δ Θ : Ctx sig} (value : Expr Γ)
    (σ : Ren sig Γ Δ) (ρ : Ren sig Δ Θ) (channel : Var Θ .nm) :
    server (NamePassing.rename σ value) ρ channel =
      server value (fun s x => ρ s (σ s x)) channel := by
  simp only [server, listener_source_rename]

theorem server_weaken {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel : Var Δ .nm) :
    weaken (server value ρ channel) = server value (push ρ) (.succ channel) :=
  server_target_rename value ρ (fun _ x => .succ x) channel

theorem server_under_definition {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel : Var Δ .nm) :
    server (NamePassing.weaken value) (liftRen ρ [.nm]) (.succ channel) =
      weaken (server value ρ channel) := by
  unfold NamePassing.weaken
  rw [server_source_rename, server_weaken]
  rfl

theorem modulo_parL {Γ : Ctx sig} {p p' : Proc Γ} (frame : Proc Γ)
    (step : StepModulo p p') : StepModulo (par p frame) (par p' frame) := by
  obtain ⟨source, target, before, firing, after⟩ := step
  exact ⟨par source frame, par target frame,
    .par before (.refl frame), .parL frame firing, .par after (.refl frame)⟩

theorem modulo_nu {Γ : Ctx sig} {p p' : Proc (.nm :: Γ)}
    (step : StepModulo p p') : StepModulo (nu p) (nu p') := by
  obtain ⟨source, target, before, firing, after⟩ := step
  exact ⟨nu source, nu target, .nu before, .nu firing, .nu after⟩

theorem modulo_congr {Γ : Ctx sig} {p q p' q' : Proc Γ}
    (before : StructuralEq p q) (step : StepModulo q q')
    (after : StructuralEq q' p') : StepModulo p p' := by
  obtain ⟨source, target, initial, firing, final⟩ := step
  exact ⟨source, target, .trans before initial, firing, .trans final after⟩

private theorem frame_exchange {Γ : Ctx sig} (p frame environment : Proc Γ) :
    StructuralEq (par (par p frame) environment) (par (par p environment) frame) :=
  .trans (.parAssoc p frame environment)
    (.trans (.par (.refl p) (.parComm frame environment))
      (.symm (.parAssoc p environment frame)))

/-- A selected environment communication preserves the additional active
component at its supplied endpoint; it does not select a competing event. -/
theorem modulo_frame_environment {Γ : Ctx sig} {p p' environment : Proc Γ}
    (frame : Proc Γ) (step : StepModulo (par p environment) (par p' environment)) :
    StepModulo (par (par p frame) environment) (par (par p' frame) environment) :=
  modulo_congr (frame_exchange p frame environment) (modulo_parL frame step)
    (.symm (frame_exchange p' frame environment))

theorem modulo_scoped_environment {Γ : Ctx sig} {p p' : Proc (.nm :: Γ)}
    (environment : Proc Γ)
    (step : StepModulo (par p (weaken environment)) (par p' (weaken environment))) :
    StepModulo (par (nu p) environment) (par (nu p') environment) :=
  modulo_congr (.nuPar p environment) (modulo_nu step)
    (.symm (.nuPar p' environment))

theorem modulo_frame_consumption {Γ : Ctx sig} {p p' declaration remainder : Proc Γ}
    (frame : Proc Γ)
    (step : StepModulo (par p (par declaration remainder)) (par p' remainder)) :
    StepModulo (par (par p frame) (par declaration remainder))
      (par (par p' frame) remainder) :=
  modulo_congr (frame_exchange p frame (par declaration remainder))
    (modulo_parL frame step) (frame_exchange p' remainder frame)

theorem modulo_scoped_consumption {Γ : Ctx sig} {p p' : Proc (.nm :: Γ)}
    (declaration remainder : Proc Γ)
    (step : StepModulo (par p (par (weaken declaration) (weaken remainder)))
      (par p' (weaken remainder))) :
    StepModulo (par (nu p) (par declaration remainder)) (par (nu p') remainder) :=
  modulo_congr (.nuPar p (par declaration remainder)) (modulo_nu step)
    (.symm (.nuPar p' remainder))

/-- A selected one-shot declaration is consumed while the supplied frame is
retained. Context traversal uses only structural administration. -/
theorem contextual_listener_consumed {Γ Δ : Ctx sig} {name : Var Γ .nm}
    {value source target : Expr Γ}
    (fetch : NamePassing.Environment.FetchAt name value source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) (remainder : Proc Δ) :
    StepModulo (par (compile source ρ result)
      (par (listener value ρ (ρ _ name)) remainder))
      (par (compile target ρ result) remainder) := by
  induction fetch generalizing Δ with
  | here name value =>
      apply modulo_congr
        (.symm (.parAssoc (compile (.var name) ρ result)
          (listener value ρ (ρ _ name)) remainder))
      · apply modulo_parL remainder
        exact (fetch_preserved name value ρ result).toModulo
      · exact .refl _
  | app argument fetch ih =>
      apply modulo_scoped_consumption
      apply modulo_frame_consumption
      simpa only [listener_weaken, push] using ih (push ρ) .zero (weaken remainder)
  | @defn Γ name value stored body body' fetch ih =>
      apply modulo_scoped_consumption
      apply modulo_frame_consumption
      have selected := ih (liftRen ρ [.nm]) (.succ result) (weaken remainder)
      rw [show liftRen ρ [Srt.nm] Srt.nm (.succ name) = .succ (ρ _ name) from rfl] at selected
      rw [listener_under_definition] at selected
      exact selected
  | carrier subject stored fetch ih =>
      exact modulo_frame_consumption
        (inp1 (.var (ρ _ subject)) (compile stored (push ρ) .zero)) (ih ρ result remainder)

/-- One unary fetch unfolds one copy and retains the same persistent server. -/
theorem persistent_fetch {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel result : Var Δ .nm) :
    StepModulo (par (out1 (.var channel) (.var result)) (server value ρ channel))
      (par (compile value ρ result) (server value ρ channel)) := by
  let output := out1 (.var channel) (.var result)
  let listener := inp1 (.var channel) (compile value (push ρ) .zero)
  refine ⟨par (par output listener) (rep listener),
    par (compile value ρ result) (rep listener), ?_, ?_, .refl _⟩
  · exact .trans (.par (.refl output) (.repUnfold listener))
      (.symm (.parAssoc output listener (rep listener)))
  · apply Step.parL
    have firing := Step.comm1 (.var channel) (.var result) (compile value (push ρ) .zero)
    rw [fetch_endpoint] at firing
    exact firing

/-- The supplied return of the selected server communication is determined
by actual opening of its result binder, and the persistent server is unchanged. -/
theorem persistent_firing_iff {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (channel result : Var Δ .nm) (endpoint : Proc Δ) :
    Step (par
      (par (out1 (.var channel) (.var result))
        (inp1 (.var channel) (compile value (push ρ) .zero)))
      (server value ρ channel))
      (par endpoint (server value ρ channel)) ↔
    endpoint = compile value ρ result := by
  constructor
  · intro step
    cases step with
    | parL frame communication =>
        cases communication with
        | comm1 => exact fetch_endpoint value ρ result
        | parL frame impossible => cases impossible
        | parR frame impossible => cases impossible
    | parR client impossible => cases impossible
  · intro equal
    subst endpoint
    apply Step.parL
    have firing := Step.comm1 (.var channel) (.var result) (compile value (push ρ) .zero)
    rw [fetch_endpoint] at firing
    exact firing

/-- Every independently selected source occurrence is fetched by one actual
target communication, through arbitrarily nested active contexts and fresh
definition binders. The exact persistent environment is retained. -/
theorem contextual_fetch_preserved {Γ Δ : Ctx sig} {name : Var Γ .nm}
    {value source target : Expr Γ}
    (fetch : NamePassing.Environment.FetchAt name value source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (par (compile source ρ result) (server value ρ (ρ _ name)))
      (par (compile target ρ result) (server value ρ (ρ _ name))) := by
  apply modulo_congr
    (.par (.refl _) (.repUnfold (listener value ρ (ρ _ name))))
  · exact contextual_listener_consumed fetch ρ result (server value ρ (ρ _ name))
  · exact .refl _

/-- A contextual carrier fetch consumes its single declaration and returns
the exact translated continuation. Persistent lookup reuses this same theorem. -/
theorem carrier_fetch_preserved {Γ Δ : Ctx sig} {name : Var Γ .nm}
    {value source target : Expr Γ}
    (fetch : NamePassing.Environment.FetchAt name value source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile (.carrier name value source) ρ result)
      (compile target ρ result) := by
  apply modulo_congr
    (.par (.refl _) (.symm (.parUnit (listener value ρ (ρ _ name)))))
  · exact contextual_listener_consumed fetch ρ result nil
  · exact .parUnit _

theorem definition_body_weaken {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    compile (NamePassing.weaken value) (liftRen ρ [.nm]) (.succ result) =
      weaken (compile value ρ result) := by
  unfold NamePassing.weaken
  rw [compile_source_rename]
  exact (compile_target_rename value ρ (fun _ x => .succ x) result).symm

/-- Persistent definition lookup preserves the translated source endpoint,
including its retained definition; no final answer is reconstructed afterward. -/
theorem definition_fetch_preserved {Γ Δ : Ctx sig} (value : Expr Γ)
    {body body' : Expr (.nm :: Γ)}
    (fetch : NamePassing.Environment.FetchAt .zero (NamePassing.weaken value) body body')
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile (.defn value body) ρ result)
      (compile (.defn value body') ρ result) := by
  apply modulo_nu
  have selected := contextual_fetch_preserved fetch (liftRen ρ [.nm]) (.succ result)
  unfold NamePassing.weaken at selected
  rw [server_source_rename] at selected
  exact selected

/-- All source communications, including retained definition reads and their
active contextual closure, compile to one target communication modulo structural
administration at the actual endpoints. -/
theorem step_preserved {Γ Δ : Ctx sig} {kind : NamePassing.Environment.Action}
    {source target : Expr Γ} (step : NamePassing.Environment.Step kind source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile source ρ result) (compile target ρ result) := by
  induction step generalizing Δ with
  | beta body argument => exact beta_preserved body argument ρ result
  | carrierFetch name value fetch => exact carrier_fetch_preserved fetch ρ result
  | environmentFetch value fetch => exact definition_fetch_preserved value fetch ρ result
  | app argument step ih =>
      exact modulo_nu (modulo_parL
        (out2 (.var .zero) (.var (.succ (ρ _ argument))) (.var (.succ result)))
        (ih (push ρ) .zero))
  | defn value step ih =>
      exact modulo_nu (modulo_parL
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)))
        (ih (liftRen ρ [.nm]) (.succ result)))
  | carrier name value step ih =>
      exact modulo_parL (inp1 (.var (ρ _ name)) (compile value (push ρ) .zero))
        (ih ρ result)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment
