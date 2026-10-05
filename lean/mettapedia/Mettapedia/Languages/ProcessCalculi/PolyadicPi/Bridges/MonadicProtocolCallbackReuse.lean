import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRegistryReindex
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

/-!
# Reusing an unused bound callback position

The receiver creates a genuine fresh private name. An offered occurrence's
older reserved callback is unused. Exchanging those bound names and removing
the now-unused binder compares the actual fresh receiver endpoint with the
same endpoint placed at the occurrence's callback position. All names remain
under their original private telescope; no ambient name is identified with
the freshly allocated name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackReuse

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Capabilities RuntimeState ScopedActiveFrontier

/-- Contract two adjacent bound names only when the older one is absent
from the exact supplied body. -/
theorem adjacent {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ))
    (unused : countVar (Var.succ Var.zero : Var (.nm :: .nm :: Γ) .nm) body = 0) :
    StructuralEq (nu (nu body)) (nu (inst body (.var .zero))) := by
  have swappedUnused : countVar (Var.zero : Var (.nm :: .nm :: Γ) .nm)
      (rename swapRen body) = 0 := by
    have counted := ScopedOpening.count_swap (.succ .zero) body
    change countVar (Var.zero : Var (.nm :: .nm :: Γ) .nm) (rename swapRen body) =
      countVar (Var.succ Var.zero : Var (.nm :: .nm :: Γ) .nm) body at counted
    exact counted.trans unused
  obtain ⟨retained, _, weakened⟩ := exists_unweaken (rename swapRen body) swappedUnused
  have original : body = rename swapRen (weaken retained) := by
    calc
      body = rename swapRen (rename swapRen body) :=
        (rename_exchange_involutive (S := sig) Srt.nm Srt.nm body).symm
      _ = rename swapRen (weaken retained) := congrArg (rename swapRen) weakened.symm
  have restored : inst body (.var .zero) = retained := by
    rw [original, inst, weaken, rename_comp, bind_rename]
    calc
      _ = bind (fun _ name => Term.var name : Sub sig (.nm :: Γ) (.nm :: Γ)) retained := by
        congr 1
        funext sort name
        cases name <;> rfl
      _ = retained := bind_id retained
  refine (StructuralEq.nuSwap body).trans ?_
  rw [← weakened, restored]
  exact .nu (.nuUnused retained)

/-- Move the new innermost name past an existing callback/session pair. -/
def pastPair {Γ : Ctx sig} : Ren sig (.nm :: .nm :: .nm :: Γ) (.nm :: .nm :: .nm :: Γ) :=
  fun sort name => liftRen swapRen [.nm] sort (swapRen sort name)

theorem move_fresh_out {Γ : Ctx sig} (body : Proc (.nm :: .nm :: .nm :: Γ)) :
    StructuralEq (nu (nu (nu body))) (nu (nu (nu (rename pastPair body)))) := by
  have inner := StructuralEq.nu (StructuralEq.nuSwap body)
  have outer := StructuralEq.nuSwap (nu (rename swapRen body))
  rw [rename_nu, rename_comp] at outer
  exact inner.trans outer

theorem inst_past_pair {Γ : Ctx sig} (body : Proc (.nm :: .nm :: .nm :: Γ))
    (name : Var Γ .nm) :
    inst (nu (nu (rename pastPair body))) (.var name) =
      nu (nu (inst body (.var (.succ (.succ name))))) := by
  change nu (nu (bind (liftSub (liftSub (extend (.var name)) [.nm]) [.nm])
    (rename pastPair body))) = nu (nu (bind (extend (.var (.succ (.succ name)))) body))
  rw [bind_rename]
  apply congrArg (fun process => nu (nu process))
  congr 1
  funext sort item
  cases item with
  | zero => rfl
  | succ item => cases item with
    | zero => rfl
    | succ item => cases item <;> rfl

theorem count_past_pair {Γ : Ctx sig} (body : Proc (.nm :: .nm :: .nm :: Γ))
    (name : Var Γ .nm) :
    countVar (Var.succ name : Var (.nm :: Γ) .nm) (nu (nu (rename pastPair body))) =
      countVar (Var.succ (Var.succ (Var.succ name))) body := by
  simp only [nu, countVar, countVarArgs, weakenVar, Nat.add_zero]
  refine countVar_rename_of_reflect pastPair (.succ (.succ (.succ name))) ?_ body
  intro sort item
  cases item with
  | zero => rfl
  | succ item => cases item with
    | zero => rfl
    | succ item => cases item <;> rfl

/-- The exact newly allocated callback can replace any unused reserved
callback in the already bound occurrence telescope. Other owners and their
session names are retained; the supplied body and endpoint are unchanged. -/
theorem private_callback : ∀ {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (freshBody : Proc (.nm :: World n Γ)),
    countVar (Var.succ (key n owner .callback)) freshBody = 0 →
      StructuralEq ((privateScope n).close (nu freshBody))
        ((privateScope n).close (inst freshBody (.var (key n owner .callback))))
  | _, 0, owner, _, _ => Fin.elim0 owner
  | _Γ, n + 1, ⟨0, _⟩, freshBody, unused => by
      simp only [privateScope, Scope.close_append, Scope.close]
      change StructuralEq ((privateScope n).close (nu (nu (nu freshBody))))
        ((privateScope n).close (nu (nu (inst freshBody (.var .zero)))))
      exact (privateScope n).congr (.nu (adjacent freshBody unused))
  | Γ, n + 1, ⟨i + 1, bound⟩, freshBody, unused => by
      let owner : Fin n := ⟨i, Nat.lt_of_succ_lt_succ bound⟩
      dsimp only [World, privatePrefix] at freshBody unused ⊢
      have retainedUnused : countVar (Var.succ (key (Γ := Γ) n owner .callback))
          (nu (nu (rename pastPair freshBody))) = 0 :=
        (count_past_pair freshBody (key n owner .callback)).trans unused
      have retained := private_callback n owner (nu (nu (rename pastPair freshBody))) retainedUnused
      rw [inst_past_pair] at retained
      simp only [privateScope]
      dsimp only [World, privatePrefix] at ⊢
      rw [Scope.close_append, Scope.close_append]
      change StructuralEq ((privateScope n).close (nu (nu (nu freshBody))))
        ((privateScope n).close
          (nu (nu (inst freshBody (.var (.succ (.succ (key n owner .callback))))))))
      exact ((privateScope n).congr (move_fresh_out freshBody)).trans retained

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackReuse
