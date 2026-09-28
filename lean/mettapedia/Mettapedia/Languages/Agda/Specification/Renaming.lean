import Mettapedia.Languages.Agda.Specification.Determinism

/-!
# Capture-avoiding transport of the reference computations

Renamings commute with finite hereditary application and binder instantiation.
The substitution theorem is stated for a commuting square of source and target
renamings, so its binder case verifies the interaction of weakening and lifting.
-/

namespace Mettapedia.Languages.Agda.Specification

theorem Term.rename_weaken (t : Term n) (ρ : Renaming n m) :
    t.weaken.rename (Renaming.lift ρ) = (t.rename ρ).weaken := by
  simp only [Term.weaken, Term.rename_comp]
  rfl

theorem Substitution.lift_commutes
    {σ : Substitution n m} {σ' : Substitution n' m'}
    {ρ : Renaming n n'} {τ : Renaming m m'}
    (h : ∀ i, σ' (ρ i) = (σ i).rename τ) :
    ∀ i, lift σ' (Renaming.lift ρ i) = (lift σ i).rename (Renaming.lift τ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Renaming.lift_succ, lift_succ, Term.rename_weaken]
    exact congrArg Term.weaken (h j)

theorem Substitution.single_commutes (t : Term n) (ρ : Renaming n m) :
    ∀ i, single (t.rename ρ) (Renaming.lift ρ i) = (single t i).rename ρ := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

mutual
  /-- Renaming preserves each finite spine-application derivation. -/
  def Apply.mapRenaming {t u : Term n} {es : Spine n}
      (h : Apply t es u) (ρ : Renaming n m) :
      Apply (t.rename ρ) (es.rename ρ) (u.rename ρ) := by
    match h with
    | .nil t => exact .nil (t.rename ρ)
    | .var i es e fs =>
      simpa only [Term.rename, Spine.rename, Spine.rename_append] using
        Apply.var (ρ i) (es.rename ρ) (e.rename ρ) (fs.rename ρ)
    | .defn f es e fs =>
      simpa only [Term.rename, Spine.rename, Spine.rename_append] using
        Apply.defn f (es.rename ρ) (e.rename ρ) (fs.rename ρ)
    | .con c es e fs =>
      simpa only [Term.rename, Spine.rename, Spine.rename_append] using
        Apply.con c (es.rename ρ) (e.rename ρ) (fs.rename ρ)
    | .lam hi ha => exact .lam (hi.mapRenaming ρ) (ha.mapRenaming ρ)

  /-- Fresh binders are lifted; `NoAbs` continues in the original scope. -/
  def Instantiate.mapRenaming {b : Abs n} {t u : Term n}
      (h : Instantiate b t u) (ρ : Renaming n m) :
      Instantiate (b.rename ρ) (t.rename ρ) (u.rename ρ) := by
    match h with
    | .bind hs =>
      exact .bind (hs.mapRenaming (Renaming.lift ρ) ρ _
        (Substitution.single_commutes _ ρ))
    | .noBind t u => exact .noBind (t.rename ρ) (u.rename ρ)

  /-- Substitution is natural in any commuting square of renamings. -/
  def Substitute.mapRenaming {σ : Substitution n m} {t : Term n} {u : Term m}
      (h : Substitute σ t u) (ρ : Renaming n n') (τ : Renaming m m')
      (σ' : Substitution n' m') (comm : ∀ i, σ' (ρ i) = (σ i).rename τ) :
      Substitute σ' (t.rename ρ) (u.rename τ) := by
    match h with
    | .var (i := i) he ha =>
      apply Substitute.var (he.mapRenaming ρ τ σ' comm)
      rw [comm i]
      exact ha.mapRenaming τ
    | .defn f he => exact .defn f (he.mapRenaming ρ τ σ' comm)
    | .con c he => exact .con c (he.mapRenaming ρ τ σ' comm)
    | .lam hb => exact .lam (hb.mapRenaming ρ τ σ' comm)
    | .pi ha hb => exact .pi (ha.mapRenaming ρ τ σ' comm) (hb.mapRenaming ρ τ σ' comm)
    | .sort _ l => exact .sort σ' l
    | .level _ l => exact .level σ' l

  def SubstituteAbs.mapRenaming {σ : Substitution n m} {b : Abs n} {c : Abs m}
      (h : SubstituteAbs σ b c) (ρ : Renaming n n') (τ : Renaming m m')
      (σ' : Substitution n' m') (comm : ∀ i, σ' (ρ i) = (σ i).rename τ) :
      SubstituteAbs σ' (b.rename ρ) (c.rename τ) := by
    match h with
    | .bind ht =>
      exact .bind (ht.mapRenaming (Renaming.lift ρ) (Renaming.lift τ)
        (Substitution.lift σ') (Substitution.lift_commutes comm))
    | .noBind ht => exact .noBind (ht.mapRenaming ρ τ σ' comm)

  def SubstituteTy.mapRenaming {σ : Substitution n m} {a : Ty n} {b : Ty m}
      (h : SubstituteTy σ a b) (ρ : Renaming n n') (τ : Renaming m m')
      (σ' : Substitution n' m') (comm : ∀ i, σ' (ρ i) = (σ i).rename τ) :
      SubstituteTy σ' (a.rename ρ) (b.rename τ) := by
    match h with
    | .el l ht => exact .el l (ht.mapRenaming ρ τ σ' comm)

  def SubstituteTyAbs.mapRenaming {σ : Substitution n m} {a : TyAbs n} {b : TyAbs m}
      (h : SubstituteTyAbs σ a b) (ρ : Renaming n n') (τ : Renaming m m')
      (σ' : Substitution n' m') (comm : ∀ i, σ' (ρ i) = (σ i).rename τ) :
      SubstituteTyAbs σ' (a.rename ρ) (b.rename τ) := by
    match h with
    | .bind ht =>
      exact .bind (ht.mapRenaming (Renaming.lift ρ) (Renaming.lift τ)
        (Substitution.lift σ') (Substitution.lift_commutes comm))
    | .noBind ht => exact .noBind (ht.mapRenaming ρ τ σ' comm)

  def SubstituteSpine.mapRenaming {σ : Substitution n m} {es : Spine n} {fs : Spine m}
      (h : SubstituteSpine σ es fs) (ρ : Renaming n n') (τ : Renaming m m')
      (σ' : Substitution n' m') (comm : ∀ i, σ' (ρ i) = (σ i).rename τ) :
      SubstituteSpine σ' (es.rename ρ) (fs.rename τ) := by
    match h with
    | .nil _ => exact .nil σ'
    | .cons ht he => exact .cons (ht.mapRenaming ρ τ σ' comm) (he.mapRenaming ρ τ σ' comm)
end

/-- The beta instance of capture avoidance, as a transformation of derivations. -/
def Substitute.rename_single {t : Term (n + 1)} {u v : Term n}
    (h : Substitute (Substitution.single u) t v) (ρ : Renaming n m) :
    Substitute (Substitution.single (u.rename ρ)) (t.rename (Renaming.lift ρ))
      (v.rename ρ) :=
  h.mapRenaming (Renaming.lift ρ) ρ _ (Substitution.single_commutes u ρ)

end Mettapedia.Languages.Agda.Specification
