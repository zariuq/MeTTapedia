import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Exchange and reindexing of sorted binders

Exchanging adjacent binders changes their variable positions, including
their sorts. The operation is involutive and commutes with reindexing the
enclosing context. Weakening and one-variable instantiation obey the same
reindexing discipline. Concrete scope-extrusion equations consume these laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature}

/-- Lifting under two successive binders agrees with the two-binder lift. -/
theorem liftRen_two {Srt : Type} {Γ Δ : List Srt}
    (ρ : (sort : Srt) → Var Γ sort → Var Δ sort) (first second : Srt) :
    liftRen (liftRen ρ [second]) [first] = liftRen ρ [first, second] := by
  funext sort x
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

/-- Exchange the two newest binders, retaining all enclosing variables. -/
def exchangeRen {Γ : Ctx S} (first second : S.Srt) :
    Ren S (first :: second :: Γ) (second :: first :: Γ)
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ old) => .succ (.succ old)

theorem exchangeRen_involutive {Γ : Ctx S} (first second : S.Srt)
    (sort : S.Srt) (x : Var (first :: second :: Γ) sort) :
    exchangeRen second first sort (exchangeRen first second sort x) = x := by
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

theorem exchangeRen_liftRen {Γ Δ : Ctx S} (ρ : Ren S Γ Δ)
    (first second sort : S.Srt) (x : Var (first :: second :: Γ) sort) :
    liftRen ρ [second, first] sort (exchangeRen first second sort x) =
      exchangeRen first second sort (liftRen ρ [first, second] sort x) := by
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

theorem rename_exchange_involutive {Γ : Ctx S} {sort : S.Srt}
    (first second : S.Srt) (term : Term S (first :: second :: Γ) sort) :
    rename (exchangeRen second first) (rename (exchangeRen first second) term) = term := by
  rw [rename_comp]
  have environment : (fun (sort : S.Srt) (x : Var (first :: second :: Γ) sort) =>
      exchangeRen second first sort (exchangeRen first second sort x)) =
      (fun _ x => x) := by
    funext sort x
    exact exchangeRen_involutive first second sort x
  rw [environment, rename_id]

theorem rename_exchange_lift {Γ Δ : Ctx S} {sort : S.Srt}
    (ρ : Ren S Γ Δ) (first second : S.Srt) (term : Term S (first :: second :: Γ) sort) :
    rename (liftRen ρ [second, first]) (rename (exchangeRen first second) term) =
      rename (exchangeRen first second) (rename (liftRen ρ [first, second]) term) := by
  rw [rename_comp, rename_comp]
  congr 1
  funext sort x
  exact exchangeRen_liftRen ρ first second sort x

theorem rename_weaken {Γ Δ : Ctx S} {sort fresh : S.Srt}
    (ρ : Ren S Γ Δ) (term : Term S Γ sort) :
    rename (liftRen ρ [fresh]) (weaken term) = weaken (rename ρ term) := by
  rw [weaken, weaken, rename_comp, rename_comp]
  rfl

theorem rename_inst {Γ Δ : Ctx S} {sort fresh : S.Srt}
    (ρ : Ren S Γ Δ) (body : Term S (fresh :: Γ) sort) (argument : Term S Γ fresh) :
    rename ρ (inst body argument) =
      inst (rename (liftRen ρ [fresh]) body) (rename ρ argument) := by
  simp only [inst, rename_bind, bind_rename]
  congr 1
  funext sort x
  cases x <;> rfl

/-- Opening with the fresh image of the distinguished variable cancels its weakening. -/
theorem inst_liftRen_succ_var {Γ : Ctx S} {sort fresh : S.Srt}
    (body : Term S (fresh :: Γ) sort) :
    inst (rename (liftRen (fun _ x => .succ x) [fresh]) body)
      (Term.var .zero : Term S (fresh :: Γ) fresh) = body := by
  rw [inst, bind_rename]
  calc
    _ = bind (fun _ x => Term.var x : Sub S (fresh :: Γ) (fresh :: Γ)) body := by
      congr 1
      funext s x
      cases x <;> rfl
    _ = body := bind_id body

end Mettapedia.OSLF.Binding
