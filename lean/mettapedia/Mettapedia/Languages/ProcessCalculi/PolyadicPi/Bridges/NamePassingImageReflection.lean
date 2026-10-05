import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-!
# Exact directed-step reflection at compiler boundaries

An injective name environment reflects the actual supplied endpoint of
every directed step starting at the literal compiler image. The source
action is independently authored by `Environment.Step`; its returned term
is not reconstructed from a quoted final answer. Private beta calls and
persistent fetches require static rearrangement and are therefore outside
this directed boundary theorem. Reflection modulo arbitrary static
rearrangements requires the additional scoped image invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingImageReflection

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

def Faithful {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) : Prop :=
  Function.Injective (environment Srt.nm)

theorem faithful_push {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (faithful : Faithful environment) : Faithful (push environment) := by
  intro first second same
  exact faithful (Var.succ.inj same)

theorem faithful_lift {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (faithful : Faithful environment) : Faithful (liftRen environment [.nm]) := by
  intro first second same
  cases first with
  | zero => cases second with
      | zero => rfl
      | succ old => cases same
  | succ old => cases second with
      | zero => cases same
      | succ other => exact congrArg Var.succ (faithful (Var.succ.inj same))

/-- Inversion of an actual parallel communication, including the precise
received endpoint and either active descent branch. -/
theorem parallel_step_cases {Γ : Ctx sig} {first second target : Proc Γ}
    (step : Step (par first second) target) :
    (∃ channel datum continuation,
      first = out1 channel datum ∧ second = inp1 channel continuation ∧
        target = inst continuation datum) ∨
    (∃ channel argument result continuation,
      first = out2 channel argument result ∧ second = inp2 channel continuation ∧
        target = openPair continuation argument result) ∨
    (∃ next, Step first next ∧ target = par next second) ∨
    (∃ next, Step second next ∧ target = par first next) := by
  cases step with
  | comm1 channel datum body => exact .inl ⟨channel, datum, body, rfl, rfl, rfl⟩
  | comm2 channel first second body => exact .inr (.inl ⟨channel, first, second, body, rfl, rfl, rfl⟩)
  | parL frame firing => exact .inr (.inr (.inl ⟨_, firing, rfl⟩))
  | parR frame firing => exact .inr (.inr (.inr ⟨_, firing, rfl⟩))

/-- A compiler image that is a unary output is a source reference request;
the data field is precisely the supplied result name. -/
theorem compile_unary_output {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (channel datum : Name Δ)
    (same : compile source environment result = out1 channel datum) :
    ∃ name : Var Γ .nm, source = .var name ∧
      channel = .var (environment _ name) ∧ datum = .var result := by
  cases source with
  | var name =>
      cases same
      exact ⟨name, rfl, rfl, rfl⟩
  | lam body => cases same
  | app function argument => cases same
  | defn value body => cases same
  | carrier name value body => cases same

/-- Literal compiler boundaries expose exactly independently authored source
actions, with the target step's actual endpoint. -/
theorem directed_step_reflected {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (faithful : Faithful environment) {endpoint : Proc Δ}
    (firing : Step (compile source environment result) endpoint) :
    ∃ action target, NamePassing.Environment.Step action source target ∧
      endpoint = compile target environment result := by
  induction source generalizing Δ with
  | var name => cases firing
  | lam body ih => cases firing
  | app function argument ih =>
      change Step (nu (par (compile function (push environment) .zero)
        (out2 (.var .zero) (.var (.succ (environment _ argument))) (.var (.succ result)))))
        endpoint at firing
      cases firing with
      | nu firing =>
          rcases parallel_step_cases firing with rootUnary | rootBinary | left | right
          · obtain ⟨channel, datum, body, _, impossible, _⟩ := rootUnary
            cases impossible
          · obtain ⟨channel, argument', result', body, _, impossible, _⟩ := rootBinary
            cases impossible
          · obtain ⟨next, step, returned⟩ := left
            obtain ⟨action, target, sourceStep, same⟩ :=
              ih (push environment) .zero (faithful_push faithful) step
            exact ⟨action, .app target argument, .app argument sourceStep,
              congrArg nu (returned.trans (congrArg (fun changed => par changed _) same))⟩
          · obtain ⟨next, impossible, _⟩ := right
            cases impossible
  | defn value body valueIH bodyIH =>
      change Step (nu (par (compile body (liftRen environment [.nm]) (.succ result))
        (server value (push environment) .zero))) endpoint at firing
      cases firing with
      | nu firing =>
          rcases parallel_step_cases firing with rootUnary | rootBinary | left | right
          · obtain ⟨channel, datum, body', _, impossible, _⟩ := rootUnary
            cases impossible
          · obtain ⟨channel, argument, result', body', _, impossible, _⟩ := rootBinary
            cases impossible
          · obtain ⟨next, step, returned⟩ := left
            obtain ⟨action, target, sourceStep, same⟩ :=
              bodyIH (liftRen environment [.nm]) (.succ result) (faithful_lift faithful) step
            exact ⟨action, .defn value target, .defn value sourceStep,
              congrArg nu (returned.trans (congrArg (fun changed => par changed _) same))⟩
          · obtain ⟨next, impossible, _⟩ := right
            cases impossible
  | carrier name value body valueIH bodyIH =>
      change Step (par (compile body environment result)
        (listener value environment (environment _ name))) endpoint at firing
      rcases parallel_step_cases firing with rootUnary | rootBinary | left | right
      · obtain ⟨channel, datum, continuation, request, receiver, returned⟩ := rootUnary
        obtain ⟨query, selected, subject, data⟩ :=
          compile_unary_output body environment result channel datum request
        have nameEqual : query = name := by
          have channelEqual : (.var (environment _ name) : Name Δ) = channel := by
            cases receiver
            rfl
          exact faithful (Term.var.inj (subject.symm.trans channelEqual.symm))
        subst query
        subst body
        cases receiver
        rw [data, fetch_endpoint] at returned
        exact ⟨.carrierFetch, value, .carrierFetch name value (.here name value), returned⟩
      · obtain ⟨channel, argument, result', continuation, _, impossible, _⟩ := rootBinary
        cases impossible
      · obtain ⟨next, step, returned⟩ := left
        obtain ⟨action, target, sourceStep, same⟩ := bodyIH environment result faithful step
        exact ⟨action, .carrier name value target, .carrier name value sourceStep,
          returned.trans (congrArg (fun changed => par changed _) same)⟩
      · obtain ⟨next, impossible, _⟩ := right
        cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingImageReflection
