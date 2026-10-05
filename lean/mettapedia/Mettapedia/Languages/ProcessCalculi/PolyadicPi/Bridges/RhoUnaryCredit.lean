import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive

/-!
# Finite administrative credit of the concrete unary compiler

Only active parallel composition and private scopes are explored. Inputs and
persistent servers retain opaque continuation bodies. A private scope carries
its finite body's latent initialization work, so opening that scope does not
create unaccounted work. The remaining request, allocator and rearming phases
carry exactly their outstanding primitive communication work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryActive

/-- Active initialization work. Guarded bodies are counted when they become
active, while each scope or server installation needs four primitive COMMs. -/
def work : {Γ : Ctx sig} → Proc Γ → Nat
  | _, .var _ => 0
  | _, .op .nil .nil => 0
  | _, .op .par (.cons first (.cons second .nil)) => work first + work second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => 0
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => 0
  | _, .op .out1 (.cons _ (.cons _ .nil)) => 0
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => 0
  | _, .op .nu (.cons body .nil) => 4 + work body
  | _, .op .rep (.cons _ .nil) => 4
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Allocated names have no influence on active initialization work. -/
theorem work_rename {Γ Δ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (environment : Ren sig Γ Δ) :
    work (rename environment process) = work process := by
  induction guarded generalizing Δ with
  | nil => simp [nil, rename, renameArgs, work]
  | par _ _ firstIH secondIH =>
      rw [rename_par]
      simp only [par, work, firstIH, secondIH]
  | inp1 channel _ ih => rw [rename_inp1]; simp [inp1, work]
  | out1 channel datum => rw [rename_out1]; simp [out1, work]
  | nu _ ih => rw [rename_nu]; simp only [nu, work, ih]
  | server channel _ ih => rw [rename_rep]; simp [rep, work]

theorem work_inst {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (datum : Var Γ .nm) :
    work (inst body (.var datum)) = work body := by
  rw [RhoUnaryNaturality.inst_variable]
  exact work_rename guarded _

/-- Credit is read directly from actual phase activities. The private client
retains the finite latent work of its suspended source body. -/
def credit {Γ : Ctx sig} : Activity Γ → Nat
  | .privateScope body _ => 1 + work body
  | .install _ _ _ | .rearm _ _ _ _ | .allocatorRearm | .seedInput => 1
  | .request => 3
  | _ => 0

def total {Γ : Ctx sig} (activities : List (Activity Γ)) : Nat :=
  (activities.map credit).sum

@[simp] theorem total_nil {Γ : Ctx sig} : total ([] : List (Activity Γ)) = 0 := rfl

@[simp] theorem total_cons {Γ : Ctx sig} (activity : Activity Γ) (activities : List (Activity Γ)) :
    total (activity :: activities) = credit activity + total activities := rfl

@[simp] theorem total_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    total (first ++ second) = total first + total second := by simp [total, List.sum_append]

theorem total_perm {Γ : Ctx sig} {first second : List (Activity Γ)}
    (permutation : first.Perm second) : total first = total second :=
  (permutation.map credit).sum_eq

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit
