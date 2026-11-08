import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionReadPort

/-!
# Controls for resolution through the read port

**The read port renames apart by itself.** The goal is `p(X)` with `X` the caller's variable `0`.
The stored clause is `p(f(X)).` with its own private variable also named `0`. Read through the port,
the clause's variable is opened at the read scope, a fresh helper apart from the caller's `X`; the
firing tells `X = f(X₍s₎)` and is admitted (`capture_free_admitted`). In the one-frame reading
with the clause built in and not renamed apart, the same pair is refused
(`Resolution.Controls.capture_refused`). After the firing, the clause occurrence is still present
and still the same stored schema (`clause_still_stored`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.ReadPort.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

inductive Fn | p | f
  deriving DecidableEq

def Fn.arity : Fn → ℕ
  | .p => 1
  | .f => 1

abbrev L := logic Fn Fn.arity

variable {V : Type} {declaration : V → MetaArity L}

/-- `p(t)`. -/
def P (t : Tm declaration) : Tm declaration := .op (.inl (.fn .p)) (argsOf 1 fun _ => t)

/-- `f(t)`. -/
def Fv (t : Tm declaration) : Tm declaration := .op (.inl (.fn .f)) (argsOf 1 fun _ => t)

abbrev Locals := locals (F := Fn) (arity := Fn.arity)
abbrev Caller := captures (F := Fn) (arity := Fn.arity) (Shared := ℕ)
abbrev Active := target (F := Fn) (arity := Fn.arity) (Shared := ℕ)

/-- The caller's goal `p(X)`. -/
def goal : Tm Caller := P (generator Caller 0)

/-- The stored clause `p(f(X)).`, its private variable also named `0`. -/
def selfApplied : Tm Locals := clauseTerm 0 (P (Fv (generator Locals 0))) Fin.elim0

/-- Every clause occurrence holds the stored clause. -/
def stored (_ : ℕ) : ContextualStoredRows.Row Locals Caller [] () :=
  ContextualStoredRows.store Locals Caller selfApplied

def before : Configuration (Tm Caller) ℕ := ⟨[], {0, 1}⟩

/-- The read scope of the firing. -/
abbrev s : ℕ := readScope (∅ : Finset ℕ) (0 : ℕ) 1 []

/-- Send the caller's `X` to `f` of the clause's opened variable. -/
def solution : Assignment Active Active
  | .inr 0 => Fv (generator Active (.inl (ScopedVar.at s 0)))
  | other => generator Active other

theorem unified :
    instantiate solution (instantiate (opened s) (P (Fv (generator Locals 0)))) =
      instantiate solution (lifted goal) := by
  with_unfolding_all rfl

/-- **Capture-free admission through the read port**: `p(X)` against the stored `p(f(X)).` is
admitted, because the read port opens the clause's `X` at a fresh scope. -/
theorem capture_free_admitted :
    ContextualActivatedStep.Valid Locals Caller (∅ : Finset ℕ) (selection (0 : ℕ) 1 []) (rule 0)
      (rows 0 goal stored) before (fun _ => lifted goal) := by
  refine (resolve_valid_iff (∅ : Finset ℕ) (0 : ℕ) 1 [] 0 goal stored (P (Fv (generator Locals 0)))
    Fin.elim0 before (fun _ => lifted goal) (by decide) rfl rfl (fun _ => lifted goal)).mpr
    ⟨List.nodup_nil, rfl, by simp [before], by simp [before], fun _ member => absurd member List.not_mem_nil, ?_⟩
  refine ⟨_, Active, solution, (models_single solution _ _).mpr ⟨?_, unified⟩⟩
  intro equation member
  exact absurd member List.not_mem_nil

/-- **The clause stays in the space, unspecialized.** -/
theorem clause_still_stored :
    1 ∈ (ContextualActivatedStep.result Locals Caller (∅ : Finset ℕ) (selection (0 : ℕ) 1 []) (rule 0)
        (rows 0 goal stored) before).present ∧
      ContextualActivatedStep.resultRows Locals Caller (selection (0 : ℕ) 1 []) (fun _ => lifted goal)
          (rows 0 goal stored) 1 =
        ContextualStoredRows.store Locals Active selfApplied :=
  ⟨resolve_clause_stays (∅ : Finset ℕ) (0 : ℕ) 1 [] 0 goal stored before (fun _ => lifted goal)
      capture_free_admitted,
    resolve_clause_row (∅ : Finset ℕ) (0 : ℕ) 1 [] 0 goal stored (P (Fv (generator Locals 0))) Fin.elim0
      before (by decide) rfl (fun _ => lifted goal) capture_free_admitted⟩

#print axioms unified
#print axioms capture_free_admitted
#print axioms clause_still_stored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.ReadPort.Controls
