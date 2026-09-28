import Mettapedia.Languages.Agda.Specification.Reduction

/-!
# Determinism of finite hereditary computation

The outputs of application, binder instantiation, and hereditary substitution
are unique whenever the corresponding finite derivations exist. No existence
or termination premise is inferred from scope alone.
-/

namespace Mettapedia.Languages.Agda.Specification

mutual
  theorem Apply.deterministic {t u v : Term n} {es : Spine n}
      (h : Apply t es u) (k : Apply t es v) : u = v := by
    match h with
    | .nil _ => exact (Apply.nil_result k).symm
    | .var _ _ _ _ => cases k; rfl
    | .defn _ _ _ _ => cases k; rfl
    | .con _ _ _ _ => cases k; rfl
    | .lam hi ha =>
      cases k with
      | lam ki ka =>
        cases Instantiate.deterministic hi ki
        exact Apply.deterministic ha ka

  theorem Instantiate.deterministic {b : Abs n} {t u v : Term n}
      (h : Instantiate b t u) (k : Instantiate b t v) : u = v := by
    match h with
    | .bind hs =>
      cases k with
      | bind ks => exact Substitute.deterministic hs ks
    | .noBind _ _ => cases k; rfl

  theorem Substitute.deterministic {σ : Substitution n m} {t : Term n} {u v : Term m}
      (h : Substitute σ t u) (k : Substitute σ t v) : u = v := by
    match h with
    | .var he ha =>
      cases k with
      | var ke ka =>
        cases SubstituteSpine.deterministic he ke
        exact Apply.deterministic ha ka
    | .defn f he =>
      cases k with
      | defn _ ke => exact congrArg (Term.defn f) (SubstituteSpine.deterministic he ke)
    | .con c he =>
      cases k with
      | con _ ke => exact congrArg (Term.con c) (SubstituteSpine.deterministic he ke)
    | .lam hb =>
      cases k with
      | lam kb => exact congrArg Term.lam (SubstituteAbs.deterministic hb kb)
    | .pi ha hb =>
      cases k with
      | pi ka kb =>
        exact congrArg₂ Term.pi (SubstituteTy.deterministic ha ka)
          (SubstituteTyAbs.deterministic hb kb)
    | .sort _ _ => cases k; rfl
    | .level _ _ => cases k; rfl

  theorem SubstituteAbs.deterministic {σ : Substitution n m} {b : Abs n} {c d : Abs m}
      (h : SubstituteAbs σ b c) (k : SubstituteAbs σ b d) : c = d := by
    match h with
    | .bind ht =>
      cases k with
      | bind kt => exact congrArg Abs.bind (Substitute.deterministic ht kt)
    | .noBind ht =>
      cases k with
      | noBind kt => exact congrArg Abs.noBind (Substitute.deterministic ht kt)

  theorem SubstituteTy.deterministic {σ : Substitution n m} {a : Ty n} {b c : Ty m}
      (h : SubstituteTy σ a b) (k : SubstituteTy σ a c) : b = c := by
    match h with
    | .el l ht =>
      cases k with
      | el _ kt => exact congrArg (Ty.el l) (Substitute.deterministic ht kt)

  theorem SubstituteTyAbs.deterministic
      {σ : Substitution n m} {a : TyAbs n} {b c : TyAbs m}
      (h : SubstituteTyAbs σ a b) (k : SubstituteTyAbs σ a c) : b = c := by
    match h with
    | .bind ht =>
      cases k with
      | bind kt => exact congrArg TyAbs.bind (SubstituteTy.deterministic ht kt)
    | .noBind ht =>
      cases k with
      | noBind kt => exact congrArg TyAbs.noBind (SubstituteTy.deterministic ht kt)

  theorem SubstituteSpine.deterministic
      {σ : Substitution n m} {es : Spine n} {fs gs : Spine m}
      (h : SubstituteSpine σ es fs) (k : SubstituteSpine σ es gs) : fs = gs := by
    match h with
    | .nil _ => cases k; rfl
    | .cons ht he =>
      cases k with
      | cons kt ke =>
        exact congrArg₂ Spine.cons
          (congrArg Elim.apply (Substitute.deterministic ht kt))
          (SubstituteSpine.deterministic he ke)
end

/-- Finite identity substitution cannot return a different term. -/
theorem Substitute.identity_result {t u : Term n}
    (h : Substitute Substitution.identity t u) : u = t :=
  h.deterministic (Substitute.identity t)

/-- The relational specification agrees with the proved total renaming action. -/
theorem Substitute.renaming_result {t : Term n} {u : Term m} (ρ : Renaming n m)
    (h : Substitute (Substitution.ofRenaming ρ) t u) : u = t.rename ρ :=
  h.deterministic (Substitute.rename t ρ)

end Mettapedia.Languages.Agda.Specification
