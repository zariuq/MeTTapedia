import Mettapedia.Languages.Agda.StaticSpecification.Syntax

/-! Structural renaming laws for the independently scoped raw syntax. -/

namespace Mettapedia.Languages.Agda.StaticSpecification

mutual
  @[simp] theorem Term.rename_id (t : Term n) :
      (t.rename id) = t := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.rename_id b )
    | .pi a b => exact congrArg₂ Term.pi (Ty.rename_id a ) (TyAbs.rename_id b )
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.rename_id f ) (Elim.rename_id e )

  @[simp] theorem Abs.rename_id (t : Abs n) :
      (t.rename id) = t := by
    match t with
    | .bind t =>
      simp only [Abs.rename, Renaming.lift_id]
      exact congrArg Abs.bind (Term.rename_id t )
    | .noBind t => exact congrArg Abs.noBind (Term.rename_id t )

  @[simp] theorem Ty.rename_id (t : Ty n) :
      (t.rename id) = t := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.rename_id t )

  @[simp] theorem TyAbs.rename_id (t : TyAbs n) :
      (t.rename id) = t := by
    match t with
    | .bind a =>
      simp only [TyAbs.rename, Renaming.lift_id]
      exact congrArg TyAbs.bind (Ty.rename_id a )
    | .noBind a => exact congrArg TyAbs.noBind (Ty.rename_id a )

  @[simp] theorem Elim.rename_id (t : Elim n) :
      (t.rename id) = t := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.rename_id t )

end

mutual
  theorem Term.rename_comp (t : Term n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .var i => rfl
    | .lam b => exact congrArg Term.lam (Abs.rename_comp b ρ τ)
    | .pi a b => exact congrArg₂ Term.pi (Ty.rename_comp a ρ τ) (TyAbs.rename_comp b ρ τ)
    | .sort k => rfl
    | .elim f e => exact congrArg₂ Term.elim (Term.rename_comp f ρ τ) (Elim.rename_comp e ρ τ)

  theorem Abs.rename_comp (t : Abs n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .bind t =>
      simp only [Abs.rename, Renaming.lift_comp]
      exact congrArg Abs.bind (Term.rename_comp t (Renaming.lift ρ) (Renaming.lift τ))
    | .noBind t => exact congrArg Abs.noBind (Term.rename_comp t ρ τ)

  theorem Ty.rename_comp (t : Ty n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .el k t => exact congrArg (Ty.el k) (Term.rename_comp t ρ τ)

  theorem TyAbs.rename_comp (t : TyAbs n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .bind a =>
      simp only [TyAbs.rename, Renaming.lift_comp]
      exact congrArg TyAbs.bind (Ty.rename_comp a (Renaming.lift ρ) (Renaming.lift τ))
    | .noBind a => exact congrArg TyAbs.noBind (Ty.rename_comp a ρ τ)

  theorem Elim.rename_comp (t : Elim n) (ρ : Renaming n m) (τ : Renaming m k) :
      (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
    match t with
    | .apply t => exact congrArg Elim.apply (Term.rename_comp t ρ τ)

end

theorem Term.rename_weaken (t : Term n) (ρ : Renaming n m) :
    t.weaken.rename (Renaming.lift ρ) = (t.rename ρ).weaken := by
  simp only [Term.weaken, Term.rename_comp]
  rfl

theorem Ty.rename_weaken (a : Ty n) (ρ : Renaming n m) :
    a.weaken.rename (Renaming.lift ρ) = (a.rename ρ).weaken := by
  simp only [Ty.weaken, Ty.rename_comp]
  rfl

@[simp] theorem Abs.open_rename (b : Abs n) (ρ : Renaming n m) :
    (b.rename ρ).open = b.open.rename (Renaming.lift ρ) := by
  cases b with
  | bind t => rfl
  | noBind t => exact (Term.rename_weaken t ρ).symm

@[simp] theorem TyAbs.open_rename (b : TyAbs n) (ρ : Renaming n m) :
    (b.rename ρ).open = b.open.rename (Renaming.lift ρ) := by
  cases b with
  | bind t => rfl
  | noBind t => exact (Ty.rename_weaken t ρ).symm

@[simp] theorem Term.app_rename (f a : Term n) (ρ : Renaming n m) :
    (f.app a).rename ρ = (f.rename ρ).app (a.rename ρ) := rfl

theorem Term.applySpine_rename (f : Term n) (es : Spine n) (ρ : Renaming n m) :
    (f.applySpine es).rename ρ = (f.rename ρ).applySpine (es.map (Elim.rename ρ)) := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => exact ih (.elim f e)

end Mettapedia.Languages.Agda.StaticSpecification
