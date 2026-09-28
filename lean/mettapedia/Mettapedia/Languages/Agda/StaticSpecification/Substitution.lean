import Mettapedia.Languages.Agda.StaticSpecification.Renaming

/-!
# Capture-avoiding substitution on raw terms

This is structural simultaneous substitution, using the de Bruijn lifting rule
from Agda 2.8.0.2 `TypeChecking.Substitute.Class`, `lookupS` on `Lift` and
`absBody` on `NoAbs`, commit `cccf42fa88eae25ccbe2623f489021d2075f6f73`.
The variable interface is `TypeChecking.Substitute.DeBruijn`. It preserves unreduced
applications and is total on raw scoped syntax; it is not hereditary evaluation.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

abbrev Substitution (n m : Nat) := Fin n → Term m

namespace Substitution

def lift (σ : Substitution n m) : Substitution (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => (σ i).weaken)

def single (a : Term n) : Substitution (n + 1) n := Fin.cases a Term.var

@[simp] theorem lift_zero (σ : Substitution n m) : lift σ 0 = .var 0 := rfl
@[simp] theorem lift_succ (σ : Substitution n m) (i : Fin n) :
    lift σ i.succ = (σ i).weaken := rfl
@[simp] theorem single_zero (a : Term n) : single a 0 = a := rfl
@[simp] theorem single_succ (a : Term n) (i : Fin n) : single a i.succ = .var i := rfl

@[simp] theorem lift_var : lift (Term.var : Substitution n n) = Term.var := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem lift_rename (σ : Substitution m k) (ρ : Renaming n m) :
    lift (σ ∘ ρ) = lift σ ∘ Renaming.lift ρ := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem rename_lift (σ : Substitution n m) (ρ : Renaming m k) :
    (fun i => (lift σ i).rename (Renaming.lift ρ)) =
      lift (fun i => (σ i).rename ρ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Term.rename_weaken (σ j) ρ

end Substitution

mutual
  def Term.subst (σ : Substitution n m) : Term n → Term m
    | .var i => σ i
    | .lam b => .lam (b.subst σ)
    | .pi a b => .pi (a.subst σ) (b.subst σ)
    | .sort k => .sort k
    | .elim f e => .elim (f.subst σ) (e.subst σ)

  def Abs.subst (σ : Substitution n m) : Abs n → Abs m
    | .bind t => .bind (t.subst (Substitution.lift σ))
    | .noBind t => .noBind (t.subst σ)

  def Ty.subst (σ : Substitution n m) : Ty n → Ty m
    | .el k t => .el k (t.subst σ)

  def TyAbs.subst (σ : Substitution n m) : TyAbs n → TyAbs m
    | .bind a => .bind (a.subst (Substitution.lift σ))
    | .noBind a => .noBind (a.subst σ)

  def Elim.subst (σ : Substitution n m) : Elim n → Elim m
    | .apply t => .apply (t.subst σ)
end

mutual
  @[simp] theorem Term.subst_id (t : Term n) :
      t.subst Term.var = t := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.subst_id b )
    | .pi a b => exact congrArg₂ Term.pi (Ty.subst_id a ) (TyAbs.subst_id b )
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.subst_id f ) (Elim.subst_id e )

  @[simp] theorem Abs.subst_id (t : Abs n) :
      t.subst Term.var = t := by
    match t with
    | .bind t =>
      simp only [Abs.subst, Substitution.lift_var]
      exact congrArg Abs.bind (Term.subst_id t )
    | .noBind t => exact congrArg Abs.noBind (Term.subst_id t )

  @[simp] theorem Ty.subst_id (t : Ty n) :
      t.subst Term.var = t := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.subst_id t )

  @[simp] theorem TyAbs.subst_id (t : TyAbs n) :
      t.subst Term.var = t := by
    match t with
    | .bind a =>
      simp only [TyAbs.subst, Substitution.lift_var]
      exact congrArg TyAbs.bind (Ty.subst_id a )
    | .noBind a => exact congrArg TyAbs.noBind (Ty.subst_id a )

  @[simp] theorem Elim.subst_id (t : Elim n) :
      t.subst Term.var = t := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.subst_id t )

end

mutual
  theorem Term.subst_rename (t : Term n) (ρ : Renaming n m) (σ : Substitution m k) :
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.subst_rename b ρ σ)
    | .pi a b => exact congrArg₂ Term.pi (Ty.subst_rename a ρ σ) (TyAbs.subst_rename b ρ σ)
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.subst_rename f ρ σ) (Elim.subst_rename e ρ σ)

  theorem Abs.subst_rename (t : Abs n) (ρ : Renaming n m) (σ : Substitution m k) :
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
    match t with
    | .bind t =>
      simp only [Abs.subst, Abs.rename, Substitution.lift_rename]
      exact congrArg Abs.bind (Term.subst_rename t (Renaming.lift ρ) (Substitution.lift σ))
    | .noBind t => exact congrArg Abs.noBind (Term.subst_rename t ρ σ)

  theorem Ty.subst_rename (t : Ty n) (ρ : Renaming n m) (σ : Substitution m k) :
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.subst_rename t ρ σ)

  theorem TyAbs.subst_rename (t : TyAbs n) (ρ : Renaming n m) (σ : Substitution m k) :
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
    match t with
    | .bind a =>
      simp only [TyAbs.subst, TyAbs.rename, Substitution.lift_rename]
      exact congrArg TyAbs.bind (Ty.subst_rename a (Renaming.lift ρ) (Substitution.lift σ))
    | .noBind a => exact congrArg TyAbs.noBind (Ty.subst_rename a ρ σ)

  theorem Elim.subst_rename (t : Elim n) (ρ : Renaming n m) (σ : Substitution m k) :
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.subst_rename t ρ σ)

end

mutual
  theorem Term.rename_subst (t : Term n) (σ : Substitution n m) (ρ : Renaming m k) :
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.rename_subst b σ ρ)
    | .pi a b => exact congrArg₂ Term.pi (Ty.rename_subst a σ ρ) (TyAbs.rename_subst b σ ρ)
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.rename_subst f σ ρ) (Elim.rename_subst e σ ρ)

  theorem Abs.rename_subst (t : Abs n) (σ : Substitution n m) (ρ : Renaming m k) :
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
    match t with
    | .bind t =>
      simp only [Abs.subst, Abs.rename]
      rw [← Substitution.rename_lift]
      exact congrArg Abs.bind (Term.rename_subst t (Substitution.lift σ) (Renaming.lift ρ))
    | .noBind t => exact congrArg Abs.noBind (Term.rename_subst t σ ρ)

  theorem Ty.rename_subst (t : Ty n) (σ : Substitution n m) (ρ : Renaming m k) :
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.rename_subst t σ ρ)

  theorem TyAbs.rename_subst (t : TyAbs n) (σ : Substitution n m) (ρ : Renaming m k) :
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
    match t with
    | .bind a =>
      simp only [TyAbs.subst, TyAbs.rename]
      rw [← Substitution.rename_lift]
      exact congrArg TyAbs.bind (Ty.rename_subst a (Substitution.lift σ) (Renaming.lift ρ))
    | .noBind a => exact congrArg TyAbs.noBind (Ty.rename_subst a σ ρ)

  theorem Elim.rename_subst (t : Elim n) (σ : Substitution n m) (ρ : Renaming m k) :
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.rename_subst t σ ρ)

end

theorem Term.subst_weaken (t : Term n) (σ : Substitution n m) :
    t.weaken.subst (Substitution.lift σ) = (t.subst σ).weaken := by
  simp only [Term.weaken, Term.subst_rename, Term.rename_subst]
  rfl

theorem Ty.subst_weaken (a : Ty n) (σ : Substitution n m) :
    a.weaken.subst (Substitution.lift σ) = (a.subst σ).weaken := by
  simp only [Ty.weaken, Ty.subst_rename, Ty.rename_subst]
  rfl

theorem Substitution.lift_comp (σ : Substitution n m) (τ : Substitution m k) :
    (fun i => (lift σ i).subst (lift τ)) = lift (fun i => (σ i).subst τ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Term.subst_weaken (σ j) τ

mutual
  theorem Term.subst_comp (t : Term n) (σ : Substitution n m) (τ : Substitution m k) :
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.subst_comp b σ τ)
    | .pi a b => exact congrArg₂ Term.pi (Ty.subst_comp a σ τ) (TyAbs.subst_comp b σ τ)
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.subst_comp f σ τ) (Elim.subst_comp e σ τ)

  theorem Abs.subst_comp (t : Abs n) (σ : Substitution n m) (τ : Substitution m k) :
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
    match t with
    | .bind t =>
      simp only [Abs.subst]
      rw [← Substitution.lift_comp]
      exact congrArg Abs.bind (Term.subst_comp t (Substitution.lift σ) (Substitution.lift τ))
    | .noBind t => exact congrArg Abs.noBind (Term.subst_comp t σ τ)

  theorem Ty.subst_comp (t : Ty n) (σ : Substitution n m) (τ : Substitution m k) :
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.subst_comp t σ τ)

  theorem TyAbs.subst_comp (t : TyAbs n) (σ : Substitution n m) (τ : Substitution m k) :
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
    match t with
    | .bind a =>
      simp only [TyAbs.subst]
      rw [← Substitution.lift_comp]
      exact congrArg TyAbs.bind (Ty.subst_comp a (Substitution.lift σ) (Substitution.lift τ))
    | .noBind a => exact congrArg TyAbs.noBind (Ty.subst_comp a σ τ)

  theorem Elim.subst_comp (t : Elim n) (σ : Substitution n m) (τ : Substitution m k) :
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.subst_comp t σ τ)

end

@[simp] theorem Ty.level_subst (a : Ty n) (σ : Substitution n m) :
    (a.subst σ).level = a.level := by cases a; rfl

@[simp] theorem TyAbs.level_subst (b : TyAbs n) (σ : Substitution n m) :
    (b.subst σ).level = b.level := by cases b <;> simp [subst, level]

@[simp] theorem Ty.universe_subst (k : Nat) (σ : Substitution n m) :
    (Ty.universe k).subst σ = Ty.universe k := rfl

@[simp] theorem Ty.pi_subst (a : Ty n) (b : TyAbs n) (σ : Substitution n m) :
    (pi a b).subst σ = pi (a.subst σ) (b.subst σ) := by
  simp [pi, subst, Term.subst]

@[simp] theorem Abs.open_subst (b : Abs n) (σ : Substitution n m) :
    (b.subst σ).open = b.open.subst (Substitution.lift σ) := by
  cases b with
  | bind t => rfl
  | noBind t => exact (Term.subst_weaken t σ).symm

@[simp] theorem TyAbs.open_subst (b : TyAbs n) (σ : Substitution n m) :
    (b.subst σ).open = b.open.subst (Substitution.lift σ) := by
  cases b with
  | bind t => rfl
  | noBind t => exact (Ty.subst_weaken t σ).symm

@[simp] theorem Term.app_subst (f a : Term n) (σ : Substitution n m) :
    (f.app a).subst σ = (f.subst σ).app (a.subst σ) := rfl

/-- Instantiate the opened abstraction using capture-avoiding substitution. -/
def Abs.instantiate (b : Abs n) (a : Term n) : Term n :=
  b.open.subst (Substitution.single a)

def TyAbs.instantiate (b : TyAbs n) (a : Term n) : Ty n :=
  b.open.subst (Substitution.single a)

@[simp] theorem Term.subst_single_weaken (t a : Term n) :
    t.weaken.subst (Substitution.single a) = t := by
  rw [Term.weaken, Term.subst_rename]
  exact Term.subst_id t

@[simp] theorem Ty.subst_single_weaken (t : Ty n) (a : Term n) :
    t.weaken.subst (Substitution.single a) = t := by
  rw [Ty.weaken, Ty.subst_rename]
  exact Ty.subst_id t

@[simp] theorem Abs.instantiate_noBind (t a : Term n) :
    (Abs.noBind t).instantiate a = t := Term.subst_single_weaken t a

@[simp] theorem TyAbs.instantiate_noBind (t : Ty n) (a : Term n) :
    (TyAbs.noBind t).instantiate a = t := Ty.subst_single_weaken t a

theorem Term.rename_single (t : Term (n + 1)) (a : Term n) (ρ : Renaming n m) :
    (t.subst (Substitution.single a)).rename ρ =
      (t.rename (Renaming.lift ρ)).subst (Substitution.single (a.rename ρ)) := by
  rw [Term.rename_subst, Term.subst_rename]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem Term.subst_single (t : Term (n + 1)) (a : Term n) (σ : Substitution n m) :
    (t.subst (Substitution.single a)).subst σ =
      (t.subst (Substitution.lift σ)).subst (Substitution.single (a.subst σ)) := by
  rw [Term.subst_comp, Term.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact (Term.subst_single_weaken (σ j) (a.subst σ)).symm

theorem Ty.rename_single (t : Ty (n + 1)) (a : Term n) (ρ : Renaming n m) :
    (t.subst (Substitution.single a)).rename ρ =
      (t.rename (Renaming.lift ρ)).subst (Substitution.single (a.rename ρ)) := by
  rw [Ty.rename_subst, Ty.subst_rename]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem Ty.subst_single (t : Ty (n + 1)) (a : Term n) (σ : Substitution n m) :
    (t.subst (Substitution.single a)).subst σ =
      (t.subst (Substitution.lift σ)).subst (Substitution.single (a.subst σ)) := by
  rw [Ty.subst_comp, Ty.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact (Term.subst_single_weaken (σ j) (a.subst σ)).symm

@[simp] theorem Abs.instantiate_rename (b : Abs n) (a : Term n) (ρ : Renaming n m) :
    (b.rename ρ).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [Abs.instantiate, Abs.open_rename, Term.rename_single]

@[simp] theorem Abs.instantiate_subst (b : Abs n) (a : Term n) (σ : Substitution n m) :
    (b.subst σ).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [Abs.instantiate, Abs.open_subst, Term.subst_single]

@[simp] theorem TyAbs.instantiate_rename (b : TyAbs n) (a : Term n) (ρ : Renaming n m) :
    (b.rename ρ).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [TyAbs.instantiate, TyAbs.open_rename, Ty.rename_single]

@[simp] theorem TyAbs.instantiate_subst (b : TyAbs n) (a : Term n) (σ : Substitution n m) :
    (b.subst σ).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [TyAbs.instantiate, TyAbs.open_subst, Ty.subst_single]

/-- Opening a weakened binder with the newest variable recovers its body. -/
@[simp] theorem Term.rename_lift_single_var (t : Term (n + 1)) :
    (t.rename (Renaming.lift Fin.succ)).subst (Substitution.single (.var 0)) = t := by
  rw [Term.subst_rename]
  have env : Substitution.single (Term.var (0 : Fin (n + 1))) ∘
      Renaming.lift Fin.succ = Term.var := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [env, Term.subst_id]

/-- Opening a weakened binder with the newest variable recovers its body. -/
@[simp] theorem Ty.rename_lift_single_var (t : Ty (n + 1)) :
    (t.rename (Renaming.lift Fin.succ)).subst (Substitution.single (.var 0)) = t := by
  rw [Ty.subst_rename]
  have env : Substitution.single (Term.var (0 : Fin (n + 1))) ∘
      Renaming.lift Fin.succ = Term.var := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [env, Ty.subst_id]

@[simp] theorem TyAbs.instantiate_weaken_var (b : TyAbs n) :
    (b.rename Fin.succ).instantiate (.var 0) = b.open := by
  simp only [TyAbs.instantiate, TyAbs.open_rename, Ty.rename_lift_single_var]

theorem Term.applySpine_subst (f : Term n) (es : Spine n) (σ : Substitution n m) :
    (f.applySpine es).subst σ = (f.subst σ).applySpine (es.map (Elim.subst σ)) := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => exact ih (.elim f e)

end Mettapedia.Languages.Agda.StaticSpecification
