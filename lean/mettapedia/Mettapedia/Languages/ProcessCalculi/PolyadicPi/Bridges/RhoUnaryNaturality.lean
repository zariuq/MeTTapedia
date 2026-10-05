import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryClosing

/-!
# Source-name reindexing and the concrete scoped rho compiler

The source uses intrinsic sorted variables. Reindexing these variables and
pulling the supplied target name environment back along the same map give
identical compiled code. This law also handles the extra stored-code binders
of persistent rho servers; they are target implementation binders rather
than additional source variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNaturality

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryClosing

/-- The semantic environment is pulled back along source reindexing. -/
def pullWorld {Γ Δ : Ctx sig} {depth : Nat} (world : World Δ depth) (nameMap : Ren sig Γ Δ) :
    World Γ depth := fun name => world (nameMap .nm name)

@[simp] theorem pullWorld_lift {Γ Δ : Ctx sig} {depth : Nat}
    (world : World Δ depth) (nameMap : Ren sig Γ Δ) :
    pullWorld (liftWorld world) (liftRen nameMap [.nm]) = liftWorld (pullWorld world nameMap) := by
  funext name
  cases name <;> rfl

@[simp] theorem pullWorld_serverHandler {Γ Δ : Ctx sig} {depth : Nat}
    (world : World Δ depth) (nameMap : Ren sig Γ Δ) :
    pullWorld (serverHandlerWorld world) (liftRen nameMap [.nm]) =
      serverHandlerWorld (pullWorld world nameMap) := by
  funext name
  cases name <;> rfl

@[simp] theorem pullWorld_storedHandler {Γ Δ : Ctx sig} {depth : Nat}
    (world : World Δ depth) (nameMap : Ren sig Γ Δ) :
    pullWorld (storedHandlerWorld world) (liftRen nameMap [.nm]) =
      storedHandlerWorld (pullWorld world nameMap) := by
  funext name
  cases name <;> rfl

@[simp] theorem evalName_rename {Γ Δ : Ctx sig} {depth : Nat}
    (world : World Δ depth) (nameMap : Ren sig Γ Δ) (name : Name Γ) :
    evalName world (rename nameMap name) = evalName (pullWorld world nameMap) name := by
  cases name with
  | var name => rfl
  | op op args => cases op

/-- The actual compiler commutes with every sorted source-name nameMap. -/
theorem compile_rename {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process) :
    ∀ {Δ : Ctx sig} {depth : Nat} (world : World Δ depth) (nameMap : Ren sig Γ Δ),
      compile world (rename nameMap process) = compile (pullWorld world nameMap) process := by
  induction guarded with
  | nil => intro Δ depth world nameMap; simp [nil, compile, rename, renameArgs]
  | par firstGuarded secondGuarded firstIH secondIH =>
      intro Δ depth world nameMap
      rw [rename_par]
      simp [par, compile, firstIH, secondIH]
  | inp1 channel bodyGuarded ih =>
      intro Δ depth world nameMap
      rw [rename_inp1]
      have bodyEq := ih (liftWorld world) (liftRen nameMap [.nm])
      rw [pullWorld_lift] at bodyEq
      simp [inp1, compile, bodyEq]
  | out1 channel datum =>
      intro Δ depth world nameMap
      rw [rename_out1]
      simp [out1, compile]
  | nu bodyGuarded ih =>
      intro Δ depth world nameMap
      rw [rename_nu]
      have bodyEq := ih (liftWorld world) (liftRen nameMap [.nm])
      rw [pullWorld_lift] at bodyEq
      simp [nu, compile, bodyEq]
  | server channel bodyGuarded ih =>
      intro Δ depth world nameMap
      rw [rename_rep, rename_inp1]
      have handlerEq := ih (serverHandlerWorld world) (liftRen nameMap [.nm])
      have storedEq := ih (storedHandlerWorld world) (liftRen nameMap [.nm])
      rw [pullWorld_serverHandler] at handlerEq
      rw [pullWorld_storedHandler] at storedEq
      simp [rep, inp1, compile, handlerEq, storedEq]

/-- Name opening is the existing sorted reindexing, rather than a separate
substitution authority for the compiler. -/
theorem inst_variable {Γ : Ctx sig} (body : Proc (.nm :: Γ)) (datum : Var Γ .nm) :
    inst body (.var datum) = rename (nameRen datum) body := by
  unfold inst
  have environment : extend (Term.var datum) =
      (fun sort name => Term.var (nameRen datum sort name)) := by
    funext sort name
    cases name <;> rfl
  rw [environment, bind_var_eq_rename]

/-- Exact compiler naturality at the communication continuation. -/
theorem compile_inst_variable {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) {depth : Nat} (world : World Γ depth) (datum : Var Γ .nm) :
    compile world (inst body (.var datum)) = compile (pullWorld world (nameRen datum)) body := by
  rw [inst_variable, compile_rename guarded]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNaturality
