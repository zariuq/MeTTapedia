import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic

/-!
# Scoped function-service protocol contexts

A component is a family of pi programs parameterized by its free-name map and
result channel. Clients use binary reception, private calls, persistent
definitions and one-shot carriers. This grammar is authored with pi operations;
it contains neither quotation inspection nor arbitrary competing parallel code.
The name-passing compiler comparison is in a separate bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.ProtocolContexts

open Mettapedia.OSLF.Binding

abbrev Program (Γ : Ctx sig) := {Δ : Ctx sig} → Ren sig Γ Δ → Var Δ .nm → Proc Δ

def push {Γ Δ : Ctx sig} (names : Ren sig Γ Δ) : Ren sig Γ (.nm :: Δ) :=
  fun sort name => .succ (names sort name)

def callNames {Γ Δ : Ctx sig} (names : Ren sig Γ Δ) :
    Ren sig (.nm :: Γ) (.nm :: .nm :: Δ) := liftRen (push names) [.nm]

inductive Context (Γ : Ctx sig) : Ctx sig → Type where
  | hole : Context Γ Γ
  | reindex {Δ Θ} : Ren sig Δ Θ → Context Γ Δ → Context Γ Θ
  | receive {Δ} : Context Γ (.nm :: Δ) → Context Γ Δ
  | call {Δ} : Context Γ Δ → Var Δ .nm → Context Γ Δ
  | storedValue {Δ} : Context Γ Δ → Program (.nm :: Δ) → Context Γ Δ
  | storedBody {Δ} : Program Δ → Context Γ (.nm :: Δ) → Context Γ Δ
  | carrierValue {Δ} : Var Δ .nm → Context Γ Δ → Program Δ → Context Γ Δ
  | carrierBody {Δ} : Var Δ .nm → Program Δ → Context Γ Δ → Context Γ Δ

namespace Context

def plug {Γ : Ctx sig} : {Δ : Ctx sig} → Context Γ Δ → Program Γ → Program Δ
  | _, .hole, component => component
  | _, .reindex names inner, component =>
      fun environment result => plug inner component (fun s x => environment s (names s x)) result
  | _, .receive inner, component => fun environment result =>
      inp2 (.var result) (plug inner component (callNames environment) (.succ .zero))
  | _, .call inner argument, component => fun environment result =>
      nu (par (plug inner component (push environment) .zero)
        (out2 (.var .zero) (.var (.succ (environment _ argument))) (.var (.succ result))))
  | _, .storedValue inner body, component => fun environment result =>
      nu (par (body (liftRen environment [.nm]) (.succ result))
        (rep (inp1 (.var .zero) (plug inner component (push (push environment)) .zero))))
  | _, .storedBody value inner, component => fun environment result =>
      nu (par (plug inner component (liftRen environment [.nm]) (.succ result))
        (rep (inp1 (.var .zero) (value (push (push environment)) .zero))))
  | _, .carrierValue name inner body, component => fun environment result =>
      par (body environment result)
        (inp1 (.var (environment _ name)) (plug inner component (push environment) .zero))
  | _, .carrierBody name value inner, component => fun environment result =>
      par (plug inner component environment result)
        (inp1 (.var (environment _ name)) (value (push environment) .zero))

def compose {Γ Δ : Ctx sig} : {Θ : Ctx sig} →
    Context Δ Θ → Context Γ Δ → Context Γ Θ
  | _, .hole, inner => inner
  | _, .reindex names outer, inner => .reindex names (compose outer inner)
  | _, .receive outer, inner => .receive (compose outer inner)
  | _, .call outer argument, inner => .call (compose outer inner) argument
  | _, .storedValue outer body, inner => .storedValue (compose outer inner) body
  | _, .storedBody value outer, inner => .storedBody value (compose outer inner)
  | _, .carrierValue name outer body, inner => .carrierValue name (compose outer inner) body
  | _, .carrierBody name value outer, inner => .carrierBody name value (compose outer inner)

@[simp] theorem plug_compose {Γ Δ Θ : Ctx sig} (outer : Context Δ Θ)
    (inner : Context Γ Δ) (component : Program Γ) :
    ((outer.compose inner).plug component : Program Θ) =
      (outer.plug (inner.plug component) : Program Θ) := by
  induction outer <;> simp only [compose, plug, *]

@[simp] theorem compose_hole {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    context.compose .hole = context := by
  induction context <;> simp only [compose, *]

theorem compose_assoc {Γ Δ Θ Ξ : Ctx sig} (outer : Context Θ Ξ)
    (middle : Context Δ Θ) (inner : Context Γ Δ) :
    (outer.compose middle).compose inner = outer.compose (middle.compose inner) := by
  induction outer <;> simp only [compose, *]

end Context

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.ProtocolContexts
