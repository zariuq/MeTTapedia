import Mettapedia.OSLF.Syntax.BindingTelescopeSubstitution

/-!
# Renamings respecting raw telescope declarations

A renaming respects two raw telescopes when each target lookup is the
renamed source lookup. Formation is deliberately separate. The lifting law
accounts for the newest declaration and for every weakened older declaration.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Telescope

variable {S : Signature} {b k : S.Srt}

abbrev RawRen (S : Signature) (b : S.Srt) (n m : Nat) := Ren S (scope b n) (scope b m)

def RawRen.asSub {n m : Nat} (ρ : RawRen S b n m) : RawSub S b n m :=
  fun s var => .var (ρ s var)

theorem RawRen.bind_asSub {n m : Nat} (ρ : RawRen S b n m)
    {s : S.Srt} (term : Term S (scope b n) s) :
    bind ρ.asSub term = rename ρ term := bind_var_eq_rename ρ term

def RawRen.lift {n m : Nat} (ρ : RawRen S b n m) : RawRen S b (n + 1) (m + 1) :=
  liftRen ρ [b]

theorem RawRen.asSub_lift {n m : Nat} (ρ : RawRen S b n m) :
    ρ.lift.asSub = Telescope.lift ρ.asSub := by
  funext s var
  cases var <;> rfl

/-- Declaration compatibility; it does not assert that either telescope is formed. -/
def RawRen.Respects {n m : Nat} (ρ : RawRen S b n m)
    (Γ : RawContext S b k n) (Δ : RawContext S b k m) : Prop :=
  ∀ v : Var (scope b n) b, lookup Δ (ρ b v) = bind ρ.asSub (lookup Γ v)

theorem RawRen.Respects.lift {n m : Nat} {ρ : RawRen S b n m}
    {Γ : RawContext S b k n} {Δ : RawContext S b k m}
    (h : ρ.Respects Γ Δ) (A : RawTy S b k n) :
    ρ.lift.Respects (Γ.snoc A) (Δ.snoc (bind ρ.asSub A)) := by
  intro v
  cases v with
  | zero =>
    change weaken (bind ρ.asSub A) = bind ρ.lift.asSub (weaken A)
    rw [RawRen.asSub_lift]
    exact (bind_lift_weaken ρ.asSub A).symm
  | succ v =>
    change weaken (lookup Δ (ρ b v)) = bind ρ.lift.asSub (weaken (lookup Γ v))
    rw [h v, RawRen.asSub_lift]
    exact (bind_lift_weaken ρ.asSub (lookup Γ v)).symm

def RawRen.identity (b : S.Srt) (n : Nat) : RawRen S b n n := fun _ v => v

theorem RawRen.respects_identity {n : Nat} (Γ : RawContext S b k n) :
    (RawRen.identity b n).Respects Γ Γ :=
  fun v => (bind_id (lookup Γ v)).symm

def RawRen.projection (b : S.Srt) (n : Nat) : RawRen S b n (n + 1) :=
  fun _ v => .succ v

theorem RawRen.respects_projection {n : Nat} (Γ : RawContext S b k n) (A : RawTy S b k n) :
    (RawRen.projection b n).Respects Γ (Γ.snoc A) :=
  fun v => (bind_projection (lookup Γ v)).symm

def RawRen.comp {n m p : Nat} (ρ : RawRen S b n m) (τ : RawRen S b m p) :
    RawRen S b n p := fun s v => τ s (ρ s v)

theorem RawRen.asSub_comp {n m p : Nat} (ρ : RawRen S b n m) (τ : RawRen S b m p) :
    (ρ.comp τ).asSub = Telescope.comp ρ.asSub τ.asSub := rfl

theorem RawRen.Respects.comp {n m p : Nat} {ρ : RawRen S b n m} {τ : RawRen S b m p}
    {Γ : RawContext S b k n} {Δ : RawContext S b k m} {Θ : RawContext S b k p}
    (h : ρ.Respects Γ Δ) (h' : τ.Respects Δ Θ) : (ρ.comp τ).Respects Γ Θ := by
  intro v
  exact (h' (ρ b v)).trans
    ((congrArg (fun A => bind τ.asSub A) (h v)).trans
      (bind_compose ρ.asSub τ.asSub (lookup Γ v)))

end Mettapedia.OSLF.Binding.Telescope
