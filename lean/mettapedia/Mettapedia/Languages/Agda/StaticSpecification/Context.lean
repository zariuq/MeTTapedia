import Mettapedia.Languages.Agda.StaticSpecification.Substitution

/-!
Raw telescopes and their de Bruijn lookup. The newest type and all older types
are weakened into the extended scope, as in the `here`/`there` rules of
`logrel-mltt`, `Definition.Typed`, commit
`9d6e290064962a1987c9e1a131c2fb967d6ef928`. Scope alone does not imply formation.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

inductive RawContext : Nat → Type
  | nil : RawContext 0
  | snoc {n} (tail : RawContext n) (type : Ty n) : RawContext (n + 1)

def RawContext.lookup : {n : Nat} → RawContext n → Fin n → Ty n
  | _, .nil, i => Fin.elim0 i
  | _, .snoc Γ a, i => Fin.cases a.weaken (fun j => (Γ.lookup j).weaken) i

@[simp] theorem RawContext.lookup_zero (Γ : RawContext n) (a : Ty n) :
    (Γ.snoc a).lookup 0 = a.weaken := rfl

@[simp] theorem RawContext.lookup_succ (Γ : RawContext n) (a : Ty n) (i : Fin n) :
    (Γ.snoc a).lookup i.succ = (Γ.lookup i).weaken := rfl

/-- A raw renaming preserves the exact annotated types of variables. -/
def Renaming.Respects (Γ : RawContext n) (Δ : RawContext m) (ρ : Renaming n m) : Prop :=
  ∀ i, Δ.lookup (ρ i) = (Γ.lookup i).rename ρ

theorem Renaming.respects_id (Γ : RawContext n) : Respects Γ Γ id := by
  intro i
  exact (Ty.rename_id (Γ.lookup i)).symm

theorem Renaming.respects_weaken (Γ : RawContext n) (a : Ty n) :
    Respects Γ (Γ.snoc a) Fin.succ := fun _ => rfl

theorem Renaming.Respects.lift {Γ : RawContext n} {Δ : RawContext m}
    {ρ : Renaming n m} (h : Respects Γ Δ ρ) (a : Ty n) :
    Respects (Γ.snoc a) (Δ.snoc (a.rename ρ)) (Renaming.lift ρ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (Ty.rename_weaken a ρ).symm
  · change (Δ.lookup (ρ j)).weaken = (Γ.lookup j).weaken.rename (Renaming.lift ρ)
    rw [h j, Ty.rename_weaken]

end Mettapedia.Languages.Agda.StaticSpecification
