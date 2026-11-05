import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Name and active-process views of a rho continuation

A received name has two uses in semantic COMM: ordinary name positions
receive its quotation, while an active dereference receives the process.
This structural interpretation makes those choices from the authored term;
it does not ask a unifier to infer them from `K[x,drop(x)]`.

The source remains the existing intrinsic rho binding syntax. Quotation
sealing requires the source's separate quotation-safety contract; this
traversal alone does not select a global quotation policy for Prime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualCommunication (base zero quote output input parallel)

variable {V W : Type} {declaration : V → MetaArity base} {next : W → MetaArity base}

def drop {Γ : Ctx base} (name : Term (signature base declaration) Γ .nm) :
    Term (signature base declaration) Γ .pr := .op (.inl .drp) (.cons name .nil)

structure Environment (declaration : V → MetaArity base) (source target : Ctx base) where
  name : Var source .nm → Term (signature base declaration) target .nm
  process : Var source .pr → Term (signature base declaration) target .pr
  active : Var source .nm → Term (signature base declaration) target .pr

@[ext] theorem Environment.ext {Γ Δ : Ctx base} {first second : Environment declaration Γ Δ}
    (names : first.name = second.name) (processes : first.process = second.process)
    (active : first.active = second.active) : first = second := by
  cases first
  cases second
  cases names
  cases processes
  cases active
  rfl

def Environment.lift {Γ Δ : Ctx base} (environment : Environment declaration Γ Δ) :
    Environment declaration (.nm :: Γ) (.nm :: Δ) where
  name
    | .zero => .var .zero
    | .succ position => weaken (environment.name position)
  process
    | .succ position => weaken (environment.process position)
  active
    | .zero => drop (.var .zero)
    | .succ position => weaken (environment.active position)

mutual

def compileName {Γ Δ : Ctx base} (environment : Environment declaration Γ Δ) :
    Term base Γ .nm → Term (signature base declaration) Δ .nm
  | .var position => environment.name position
  | .op .quo (.cons body .nil) => quote (compileProcess environment body)
termination_by name => termSize name
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

def compileProcess {Γ Δ : Ctx base} (environment : Environment declaration Γ Δ) :
    Term base Γ .pr → Term (signature base declaration) Δ .pr
  | .var position => environment.process position
  | .op .nil .nil => zero
  | .op .par (.cons left (.cons right .nil)) =>
      parallel (compileProcess environment left) (compileProcess environment right)
  | .op .out (.cons channel (.cons payload .nil)) =>
      output (compileName environment channel) (compileProcess environment payload)
  | .op .inp (.cons channel (.cons body .nil)) =>
      input (compileName environment channel) (compileProcess environment.lift body)
  | .op .drp (.cons (.var position) .nil) => environment.active position
  | .op .drp (.cons (.op .quo (.cons body .nil)) .nil) => drop (quote (compileProcess environment body))
termination_by process => termSize process
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

end

def Environment.map {Γ Δ : Ctx base} (assignment : Assignment declaration next)
    (environment : Environment declaration Γ Δ) : Environment next Γ Δ where
  name position := instantiate assignment (environment.name position)
  process position := instantiate assignment (environment.process position)
  active position := instantiate assignment (environment.active position)

theorem Environment.map_lift {Γ Δ : Ctx base} (assignment : Assignment declaration next)
    (environment : Environment declaration Γ Δ) :
    (environment.map assignment).lift = environment.lift.map assignment := by
  cases environment
  apply Environment.ext <;> funext position <;> cases position <;>
    simp [Environment.map,Environment.lift,drop,instantiate,instantiateArgs,weaken,
      ContextualFamily.instantiate_rename]

mutual

theorem compileName_instantiate {Γ Δ : Ctx base} (assignment : Assignment declaration next)
    (environment : Environment declaration Γ Δ) : ∀ name : Term base Γ .nm,
    instantiate assignment (compileName environment name) = compileName (environment.map assignment) name
  | .var _ => by rw [compileName,compileName]; rfl
  | .op .quo (.cons body .nil) => by
      rw [compileName,compileName]
      change quote (instantiate assignment (compileProcess environment body)) = _
      rw [compileProcess_instantiate]
termination_by name => termSize name
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

theorem compileProcess_instantiate {Γ Δ : Ctx base} (assignment : Assignment declaration next)
    (environment : Environment declaration Γ Δ) : ∀ process : Term base Γ .pr,
    instantiate assignment (compileProcess environment process) = compileProcess (environment.map assignment) process
  | .var _ => by rw [compileProcess,compileProcess]; rfl
  | .op .nil .nil => by rw [compileProcess,compileProcess]; rfl
  | .op .par (.cons left (.cons right .nil)) => by
      rw [compileProcess,compileProcess]
      change parallel (instantiate assignment (compileProcess environment left))
        (instantiate assignment (compileProcess environment right)) = _
      rw [compileProcess_instantiate,compileProcess_instantiate]
  | .op .out (.cons channel (.cons payload .nil)) => by
      rw [compileProcess,compileProcess]
      change output (instantiate assignment (compileName environment channel))
        (instantiate assignment (compileProcess environment payload)) = _
      rw [compileName_instantiate,compileProcess_instantiate]
  | .op .inp (.cons channel (.cons body .nil)) => by
      rw [compileProcess,compileProcess]
      change input (instantiate assignment (compileName environment channel))
        (instantiate assignment (compileProcess environment.lift body)) = _
      rw [compileName_instantiate,compileProcess_instantiate,Environment.map_lift]
  | .op .drp (.cons (.var _) .nil) => by rw [compileProcess,compileProcess]; rfl
  | .op .drp (.cons (.op .quo (.cons body .nil)) .nil) => by
      rw [compileProcess,compileProcess]
      change drop (quote (instantiate assignment (compileProcess environment body))) = _
      rw [compileProcess_instantiate]
termination_by process => termSize process
decreasing_by all_goals (simp only [termSize,argsSize]; omega)

end

def received (payload : Term (signature base declaration) [] .pr) : Environment declaration [.nm] [] where
  name | .zero => quote payload
  process | .succ impossible => nomatch impossible
  active | .zero => payload

def continuation (body : Term base [.nm] .pr) (payload : Term (signature base declaration) [] .pr) :=
  compileProcess (received payload) body

theorem received_map (assignment : Assignment declaration next) (payload : Term (signature base declaration) [] .pr) :
    (received payload).map assignment = received (instantiate assignment payload) := by
  apply Environment.ext
  · funext position
    cases position with
    | zero => rfl
    | succ impossible => nomatch impossible
  · funext position
    cases position with
    | succ impossible => nomatch impossible
  · funext position
    cases position with
    | zero => rfl
    | succ impossible => nomatch impossible

/-- Instantiating the compiled template uses the existing contextual
substitution, including underneath genuine receiver binders. -/
theorem continuation_instantiate (assignment : Assignment declaration next) (body : Term base [.nm] .pr)
    (payload : Term (signature base declaration) [] .pr) :
    instantiate assignment (continuation body payload) = continuation body (instantiate assignment payload) := by
  rw [continuation,compileProcess_instantiate,received_map]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation
