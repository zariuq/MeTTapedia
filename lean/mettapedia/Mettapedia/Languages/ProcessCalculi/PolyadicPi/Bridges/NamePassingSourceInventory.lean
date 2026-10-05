import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames

/-!
# Computing the active actor inventory directly from the lambda source

The source inventory follows only function positions and environment bodies.
Applications supply binary calls, definitions supply persistent unary servers,
and carriers supply one-shot unary listeners. The selected target channel and
ordered payload observations are proved to occur in this independent source
construction. The definition is not a target reduction or a decoded answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSourceInventory

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

universe u

/-- The source reference assignment is independent of the physical target
name representation. A bound definition extends it with its own private key. -/
abbrev ReferenceKeys (Key : Type u) (Γ : Ctx sig) := Var Γ Srt.nm → Key

/-- An independently computed inventory of active source actors and their
channel/payload keys. Neither stored values nor lambda bodies are traversed. -/
def inventory {Key : Type u} (binderKey : Origin → Key) :
    {Γ : Ctx sig} → Expr Srt.nm Γ → List Edge → ReferenceKeys Key Γ → Key →
      Set (Observation Origin Key)
  | _, .var name, address, references, result =>
      {⟨.output1, ⟨.lookup, address⟩, references name, [result]⟩}
  | _, .lam _, address, _, result => {⟨.input2, ⟨.lambda, address⟩, result, []⟩}
  | _, .app function argument, address, references, result =>
      inventory binderKey function (.function :: address) references (binderKey ⟨.privateCall, address⟩) ∪
        {⟨.output2, ⟨.application, address⟩, binderKey ⟨.privateCall, address⟩, [references argument, result]⟩}
  | _, .defn _ body, address, references, result =>
      inventory binderKey body (.definitionBody :: address)
          (ActiveMarkedNames.extend (binderKey ⟨.privateReference, address⟩) references) result ∪
        {⟨.input1, ⟨.definition, address⟩, binderKey ⟨.privateReference, address⟩, []⟩}
  | _, .carrier name _ body, address, references, result =>
      inventory binderKey body (.carrierBody :: address) references result ∪
        {⟨.input1, ⟨.carrier, address⟩, references name, []⟩}

def referenceKeys {Key : Type u} {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (keys : ActiveMarkedNames.Environment Key Δ) : ReferenceKeys Key Γ :=
  fun name => keys (environment _ name)

theorem pushed_reference_keys {Key : Type u} {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (keys : ActiveMarkedNames.Environment Key Δ) (fresh : Key) :
    referenceKeys (push environment) (ActiveMarkedNames.extend fresh keys) = referenceKeys environment keys := rfl

theorem bound_reference_keys {Key : Type u} {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (keys : ActiveMarkedNames.Environment Key Δ) (fresh : Key) :
    referenceKeys (liftRen environment [.nm]) (ActiveMarkedNames.extend fresh keys) =
      ActiveMarkedNames.extend fresh (referenceKeys environment keys) := by
  funext name
  cases name <;> rfl

/-- Every compiler clause realizes exactly the independently computed source
actor inventory, with all active reference bindings retained. -/
theorem compile_inventory {Key : Type u} (binderKey : Origin → Key) {Γ Δ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (keys : ActiveMarkedNames.Environment Key Δ) :
    observe binderKey (mark source address) (compile source environment result) keys =
      inventory binderKey source address (referenceKeys environment keys) (keys result) := by
  induction source generalizing Δ address with
  | var name => simp only [mark, compile, out1, observe, nameKey, inventory, referenceKeys]
  | lam body ih => simp only [mark, compile, inp2, observe, nameKey, inventory]
  | app function argument ih =>
      simp only [mark, compile, nu, par, out2, observe, nameKey, inventory]
      rw [ih, pushed_reference_keys]
      rfl
  | defn value body valueIH bodyIH =>
      simp only [mark, compile, nu, par, rep, inp1, observe, nameKey, inventory]
      rw [bodyIH, bound_reference_keys]
      rfl
  | carrier name value body valueIH bodyIH =>
      simp only [mark, compile, par, inp1, observe, nameKey, inventory]
      rw [bodyIH]
      rfl

/-- Exact selected actor keys from an arbitrary target firing occur in the
source inventory. The same actual exposure and continuation marks are kept
alongside those constraints for the subsequent endpoint readback. -/
theorem actual_step_has_source_inventory {Key : Type u} (binderKey : Origin → Key)
    {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (keys : ActiveMarkedNames.Environment Key Δ) {target : Proc Δ}
    (firing : StepModulo (compile source environment result) target) :
    ∃ (exposure : Exposure (compile source environment result) target)
      (traced : TracedExposure (mark source []) exposure),
      inputObservation traced.continuation (scopeEnvironment binderKey traced.binders keys) ∈
          inventory binderKey source [] (referenceKeys environment keys) (keys result) ∧
      outputObservation traced.continuation (scopeEnvironment binderKey traced.binders keys) ∈
          inventory binderKey source [] (referenceKeys environment keys) (keys result) := by
  rcases modulo_step_has_traced_origins (Origin.mk .privateCall []) (mark_fits source [] environment result) firing with
    ⟨exposure, ⟨traced⟩⟩
  refine ⟨exposure, traced, ?_, ?_⟩
  · rw [← compile_inventory]
    exact traced_input_observed binderKey traced keys
  · rw [← compile_inventory]
    exact traced_output_observed binderKey traced keys

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSourceInventory
