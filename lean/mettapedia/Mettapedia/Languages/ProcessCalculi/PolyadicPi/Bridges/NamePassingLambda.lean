import Mettapedia.Languages.LambdaCalculus.NamePassing
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic
import Mettapedia.OSLF.Syntax.Strengthening

/-!
# The name-passing lambda translation of Native Type Theory

The five clauses of Proposition 32 are interpreted over explicit scopes.
The result channel is an argument of the translation; application creates a
fresh internal channel, and lambda receives the reference and return channel
in one binary communication. Source name substitution and target renaming
are proved independently of the operational comparison.

This is the abridged name-passing dialect of Example 30, rather than the
ordinary lambda presentation or the dependent lambda-Pi calculus. The target
is the two-sort unary/binary asynchronous pi signature of Example 31, rather
than the existing monadic one-sort pi presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

abbrev Expr (Γ : Ctx sig) := NamePassing.Expr Srt.nm Γ

/-- Add a private target name without changing the source context. -/
def push {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) : Ren sig Γ (.nm :: Δ) :=
  fun s x => .succ (ρ s x)

/-- Lambda's reference binder is first; its return-channel binder is second. -/
def callEnv {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) :
    Ren sig (.nm :: Γ) (.nm :: .nm :: Δ) := liftRen (push ρ) [.nm]

/-- Translation with an explicit environment of names and return channel. -/
def compile : {Γ Δ : Ctx sig} → Expr Γ → Ren sig Γ Δ → Var Δ .nm → Proc Δ
  | _, _, .var x, ρ, u => out1 (.var (ρ _ x)) (.var u)
  | _, _, .lam body, ρ, u =>
      inp2 (.var u) (compile body (callEnv ρ) (.succ .zero))
  | _, _, .app function argument, ρ, u =>
      nu (par (compile function (push ρ) .zero)
        (out2 (.var .zero) (.var (.succ (ρ _ argument))) (.var (.succ u))))
  | _, _, .defn value body, ρ, u =>
      nu (par (compile body (liftRen ρ [.nm]) (.succ u))
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero))))
  | _, _, .carrier name value body, ρ, u =>
      par (compile body ρ u)
        (inp1 (.var (ρ _ name)) (compile value (push ρ) .zero))

def translate {Γ : Ctx sig} (term : Expr Γ) (result : Var Γ .nm) : Proc Γ :=
  compile term (fun _ x => x) result

private theorem push_comp {Γ Δ Θ : Ctx sig} (ρ : Ren sig Γ Δ) (τ : Ren sig Δ Θ) :
    (fun s x => liftRen τ [.nm] s (push ρ s x)) =
      push (fun s x => τ s (ρ s x)) := rfl

private theorem callEnv_comp {Γ Δ Θ : Ctx sig} (ρ : Ren sig Γ Δ) (τ : Ren sig Δ Θ) :
    (fun s x => liftRen τ [.nm, .nm] s (callEnv ρ s x)) =
      callEnv (fun s x => τ s (ρ s x)) := by
  funext s x
  cases x <;> rfl

private theorem push_source_comp {Γ Δ Θ : Ctx sig}
    (σ : Ren sig Γ Δ) (ρ : Ren sig Δ Θ) :
    (fun s x => push ρ s (σ s x)) = push (fun s x => ρ s (σ s x)) := rfl

private theorem callEnv_source_comp {Γ Δ Θ : Ctx sig}
    (σ : Ren sig Γ Δ) (ρ : Ren sig Δ Θ) :
    (fun s x => callEnv ρ s (liftRen σ [.nm] s x)) =
      callEnv (fun s x => ρ s (σ s x)) := by
  funext s x
  cases x <;> rfl

/-- Source simultaneous name substitution is interpreted by composition of
the supplied name environment, including beneath source binders. -/
theorem compile_source_rename {Γ Δ Θ : Ctx sig} (term : Expr Γ)
    (σ : Ren sig Γ Δ) (ρ : Ren sig Δ Θ) (result : Var Θ .nm) :
    compile (NamePassing.rename σ term) ρ result =
      compile term (fun s x => ρ s (σ s x)) result := by
  induction term generalizing Δ Θ with
  | var x => rfl
  | lam body ih =>
      simp only [NamePassing.rename, compile, ih]
      exact congrArg (fun env => inp2 (.var result) (compile body env (.succ .zero)))
        (callEnv_source_comp σ ρ)
  | app function argument ih =>
      simp only [NamePassing.rename, compile, ih, push_source_comp]
  | defn value body ihv ihb =>
      simp only [NamePassing.rename, compile, ihv, ihb]
      have lifted :
          (fun s x => liftRen ρ [.nm] s (liftRen σ [.nm] s x)) =
            liftRen (fun s x => ρ s (σ s x)) [.nm] :=
        (liftRen_comp (S := sig) σ ρ [.nm]).symm
      exact congrArg nu (congrArg₂ par
        (congrArg (fun env => compile body env (.succ result)) lifted) rfl)
  | carrier name value body ihv ihb =>
      simp only [NamePassing.rename, compile, ihv, ihb, push_source_comp]

/-- Reindexing the translated process agrees with reindexing all source
references and its return channel. Fresh private and receiver names are fixed. -/
theorem compile_target_rename {Γ Δ Θ : Ctx sig} (term : Expr Γ)
    (ρ : Ren sig Γ Δ) (τ : Ren sig Δ Θ) (result : Var Δ .nm) :
    rename τ (compile term ρ result) =
      compile term (fun s x => τ s (ρ s x)) (τ _ result) := by
  induction term generalizing Δ Θ with
  | var x => rfl
  | lam body ih =>
      simp only [compile, rename_inp2, rename, ih, callEnv_comp, liftRen]
  | app function argument ih =>
      simp only [compile, rename_nu, rename_par, rename_out2, rename, ih,
        liftRen, push]
      rfl
  | defn value body ihv ihb =>
      simp only [compile, rename_nu, rename_par, rename_rep, rename_inp1,
        rename, ihv, ihb, liftRen]
      congr 2
      · congr 1
        exact (liftRen_comp (S := sig) ρ τ [.nm]).symm
  | carrier name value body ihv ihb =>
      simp only [compile, rename_par, rename_inp1, rename, ihv, ihb,
        push_comp, liftRen]

/-- The public translation commutes with source name substitution and its
matching target variable substitution, at the same supplied return channel. -/
theorem translate_rename {Γ Δ : Ctx sig} (term : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Γ .nm) :
    translate (NamePassing.rename ρ term) (ρ _ result) =
      rename ρ (translate term result) := by
  unfold translate
  rw [compile_source_rename, compile_target_rename]

/-- Capture-avoiding weakening keeps the target's fresh name independent. -/
theorem translate_weaken {Γ : Ctx sig} (term : Expr Γ) (result : Var Γ .nm) :
    translate (NamePassing.weaken (fresh := Srt.nm) term) (.succ result) =
      weaken (translate term result) :=
  translate_rename term (fun _ x => .succ x) result

private theorem inst_variable {Γ : Ctx sig} (body : Proc (.nm :: Γ))
    (name : Var Γ .nm) :
    inst body (.var name) = rename (nameRen name) body := by
  unfold inst
  have environments : extend (Term.var name) =
      (fun s x => Term.var (nameRen name s x)) := by
    funext s x
    cases x <;> rfl
  rw [environments, bind_var_eq_rename]

/-- A carrier's unary communication returns the translated value at the
supplied result channel, for every value and every ambient scope. -/
theorem fetch_endpoint {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    inst (compile value (push ρ) .zero) (.var result) =
      compile value ρ result := by
  rw [inst_variable, compile_target_rename]
  rfl

/-- A binary call opens the argument and return binders in their correct
order. Only the now-unused private call-channel binder remains. -/
theorem beta_endpoint {Γ Δ : Ctx sig} (body : Expr (.nm :: Γ))
    (argument : Var Γ .nm) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    openPair (compile body (callEnv (push ρ)) (.succ .zero))
        (.var (.succ (ρ _ argument))) (.var (.succ result)) =
      weaken (compile (NamePassing.instantiate body argument) ρ result) := by
  rw [openPair_variables, compile_target_rename]
  unfold weaken NamePassing.instantiate
  rw [compile_target_rename, compile_source_rename]
  have environments :
      (fun s x => pairRen (.succ (ρ _ argument)) (.succ result) s
        (callEnv (push ρ) s x)) =
      (fun s x => (ρ s (NamePassing.plugName argument s x)).succ) := by
    funext s x
    cases x <;> rfl
  exact congrArg (fun env => compile body env (.succ result)) environments

/-- Opening this binary call reflects its supplied return process. The
fresh call channel can be removed only from the actual received endpoint. -/
theorem beta_endpoint_iff {Γ Δ : Ctx sig} (body : Expr (.nm :: Γ))
    (argument : Var Γ .nm) (ρ : Ren sig Γ Δ) (result : Var Δ .nm)
    (endpoint : Proc Δ) :
    openPair (compile body (callEnv (push ρ)) (.succ .zero))
        (.var (.succ (ρ _ argument))) (.var (.succ result)) = weaken endpoint ↔
      endpoint = compile (NamePassing.instantiate body argument) ρ result := by
  rw [beta_endpoint]
  constructor
  · intro equal
    exact (rename_injective (Strengthener.ofWeaken sig Srt.nm) equal).symm
  · intro equal
    rw [equal]

private theorem binary_communication_iff {Γ : Ctx sig}
    (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ))
    (endpoint : Proc Γ) :
    Step (par (out2 channel first second) (inp2 channel body)) endpoint ↔
      endpoint = openPair body first second := by
  constructor
  · intro step
    cases step with
    | comm2 => rfl
    | parL frame impossible => cases impossible
    | parR frame impossible => cases impossible
  · intro equal
    subst endpoint
    exact .comm2 channel first second body

private theorem unary_communication_iff {Γ : Ctx sig}
    (channel datum : Name Γ) (body : Proc (.nm :: Γ)) (endpoint : Proc Γ) :
    Step (par (out1 channel datum) (inp1 channel body)) endpoint ↔
      endpoint = inst body datum := by
  constructor
  · intro step
    cases step with
    | comm1 => rfl
    | parL frame impossible => cases impossible
    | parR frame impossible => cases impossible
  · intro equal
    subst endpoint
    exact .comm1 channel datum body

/-- A supplied endpoint of the binary communication block is exactly the
translated beta result. This reflects the selected call, rather than asserting
reflection of arbitrary target schedules or structural rearrangements. -/
theorem beta_firing_iff {Γ Δ : Ctx sig} (body : Expr (.nm :: Γ))
    (argument : Var Γ .nm) (ρ : Ren sig Γ Δ) (result : Var Δ .nm)
    (endpoint : Proc Δ) :
    Step (nu (par
        (out2 (.var .zero) (.var (.succ (ρ _ argument))) (.var (.succ result)))
        (inp2 (.var .zero) (compile body (callEnv (push ρ)) (.succ .zero)))))
      (nu (weaken endpoint)) ↔
    endpoint = compile (NamePassing.instantiate body argument) ρ result := by
  constructor
  · intro step
    cases step with
    | nu firing =>
        exact (beta_endpoint_iff body argument ρ result endpoint).mp
          ((binary_communication_iff _ _ _ _ _).mp firing).symm
  · intro equal
    apply Step.nu
    apply (binary_communication_iff _ _ _ _ _).mpr
    exact ((beta_endpoint_iff body argument ρ result endpoint).mpr equal).symm

/-- Unary fetch both preserves and reflects the actual supplied endpoint. -/
theorem fetch_firing_iff {Γ Δ : Ctx sig} (name : Var Γ .nm) (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) (endpoint : Proc Δ) :
    Step (compile (.carrier name value (.var name)) ρ result) endpoint ↔
      endpoint = compile value ρ result := by
  change Step (par (out1 (.var (ρ _ name)) (.var result))
    (inp1 (.var (ρ _ name)) (compile value (push ρ) .zero))) endpoint ↔ _
  rw [unary_communication_iff, fetch_endpoint]

/-- The paper's fetch rule is one actual unary communication with precisely
the translated source target. -/
theorem fetch_preserved {Γ Δ : Ctx sig} (name : Var Γ .nm) (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    Step (compile (.carrier name value (.var name)) ρ result)
      (compile value ρ result) := by
  have firing := Step.comm1 (.var (ρ _ name)) (.var result)
    (compile value (push ρ) .zero)
  rw [fetch_endpoint] at firing
  exact firing

/-- Beta is one binary communication under the fresh call-channel scope.
Parallel commutativity selects the receiver, and eliminating the unused
private name gives exactly the translated source endpoint. -/
theorem beta_preserved {Γ Δ : Ctx sig} (body : Expr (.nm :: Γ))
    (argument : Var Γ .nm) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile (.app (.lam body) argument) ρ result)
      (compile (NamePassing.instantiate body argument) ρ result) := by
  let received := compile body (callEnv (push ρ)) (.succ .zero)
  let input := inp2 (.var .zero) received
  let output := out2 (.var .zero) (.var (.succ (ρ _ argument))) (.var (.succ result))
  refine ⟨nu (par output input),
    nu (weaken (compile (NamePassing.instantiate body argument) ρ result)),
    ?_, ?_, StructuralEq.nuUnused _⟩
  · exact StructuralEq.nu (StructuralEq.parComm input output)
  · apply Step.nu
    have firing := Step.comm2 (.var .zero) (.var (.succ (ρ _ argument)))
      (.var (.succ result)) received
    rw [show received = compile body (callEnv (push ρ)) (.succ .zero) from rfl,
      beta_endpoint] at firing
    exact firing

/-- Every displayed source rewrite has a target execution block with the
same supplied translated endpoint. No simulation assumption is required. -/
theorem rootStep_preserved {Γ Δ : Ctx sig} {source target : Expr Γ}
    (step : NamePassing.RootStep source target) (ρ : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    StepModulo (compile source ρ result) (compile target ρ result) := by
  cases step with
  | beta body argument => exact beta_preserved body argument ρ result
  | fetch name => exact (fetch_preserved name target ρ result).toModulo

private theorem modulo_parallel {Γ : Ctx sig} {p p' : Proc Γ}
    (q : Proc Γ) (step : StepModulo p p') : StepModulo (par p q) (par p' q) := by
  obtain ⟨source, target, before, firing, after⟩ := step
  exact ⟨par source q, par target q,
    .par before (.refl q), .parL q firing, .par after (.refl q)⟩

private theorem modulo_restriction {Γ : Ctx sig} {p p' : Proc (.nm :: Γ)}
    (step : StepModulo p p') : StepModulo (nu p) (nu p') := by
  obtain ⟨source, target, before, firing, after⟩ := step
  exact ⟨nu source, nu target, .nu before, .nu firing, .nu after⟩

/-- The comparison extends through all active source evaluation contexts:
the function of an application, the body of a carrier, and the body of a
definition below its name binder. Stored values and lambda bodies stay guarded. -/
theorem headStep_preserved {Γ Δ : Ctx sig} {source target : Expr Γ}
    (step : NamePassing.HeadStep source target) (ρ : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    StepModulo (compile source ρ result) (compile target ρ result) := by
  induction step generalizing Δ with
  | root rootStep => exact rootStep_preserved rootStep ρ result
  | app argument step ih =>
      exact modulo_restriction (modulo_parallel
        (out2 (.var .zero) (.var (.succ (ρ _ argument))) (.var (.succ result)))
        (ih (push ρ) .zero))
  | defn value step ih =>
      exact modulo_restriction (modulo_parallel
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)))
        (ih (liftRen ρ [.nm]) (.succ result)))
  | carrier name value step ih =>
      exact modulo_parallel (inp1 (.var (ρ _ name)) (compile value (push ρ) .zero))
        (ih ρ result)

/-- Finite source head computations yield target blocks at their actual
translated endpoints. The closure retains every supplied intermediate source. -/
theorem headPath_preserved {Γ Δ : Ctx sig} {source target : Expr Γ}
    (path : Relation.ReflTransGen NamePassing.HeadStep source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    Relation.ReflTransGen StepModulo (compile source ρ result) (compile target ρ result) := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact ih.tail (headStep_preserved step ρ result)

/-- The translated reference definition can answer a fetch via its replicated
server. The displayed abridged source roots do not provide the corresponding
definition activation. This transition is an explicit boundary for reflection. -/
theorem definition_fetch {Γ Δ : Ctx sig} (value : Expr Γ)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile (.defn value (.var .zero)) ρ result)
      (nu (par (weaken (compile value ρ result))
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero))))) := by
  let output : Proc (.nm :: Δ) := out1 (.var .zero) (.var (.succ result))
  let listener : Proc (.nm :: Δ) :=
    inp1 (.var .zero) (compile value (push (push ρ)) .zero)
  refine ⟨nu (par (par output listener) (rep listener)),
    nu (par (weaken (compile value ρ result)) (rep listener)), ?_, ?_, .refl _⟩
  · exact .nu (.trans (.par (.refl output) (.repUnfold listener))
      (.symm (.parAssoc output listener (rep listener))))
  · apply Step.nu
    apply Step.parL
    have firing := Step.comm1 (.var .zero) (.var (.succ result))
      (compile value (push (push ρ)) .zero)
    rw [fetch_endpoint] at firing
    have value_in_scope : compile value (push ρ) (.succ result) =
        weaken (compile value ρ result) :=
      (compile_target_rename value ρ (fun _ x => .succ x) result).symm
    rw [value_in_scope] at firing
    exact firing


end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
