import Mettapedia.Languages.Agda.Structural.StaticRenaming

/-!
# Typed substitutions for the structural static presentation

Every variable image carries an actual derivation at the substituted lookup
type. Lifting uses the previously proved renaming action. The transformation
of judgment trees is then an induction through the original rule data, not a
new substitution inference rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

structure TypedSubstitution (D : Judgment → Type) {n m : Nat}
    (Γ : RawContext n) (Δ : RawContext m) (σ : RawSub n m) where
  source : D (context Γ)
  target : D (context Δ)
  image : (v : Var (scope n) .term) → D (typed Δ (σ .term v) (bind σ (ContextGeometry.lookup Γ v)))

variable {D : Judgment → Type}

/-- Lift a typed substitution using actual renaming of its old image derivations. -/
def TypedSubstitution.lift
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Judgment}, D j → RenamingAction D j)
    {n m : Nat} {Γ : RawContext n} {Δ : RawContext m} {σ : RawSub n m}
    (d : TypedSubstitution D Γ Δ σ) {A : RawTy n}
    (domain : D (formed Γ A)) (imageType : D (formed Δ (bind σ A))) :
    TypedSubstitution D (Γ.snoc A) (Δ.snoc (bind σ A)) (Telescope.lift σ) := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let target := build (.extend Δ (bind σ A))
    (consEvidence D d.target (consEvidence D imageType (noEvidence D)))
  refine ⟨build (.extend Γ A) (consEvidence D d.source (consEvidence D domain (noEvidence D))),
    target, ?_⟩
  intro v
  cases v with
  | zero =>
    exact (congrArg (fun T => D (typed (Δ.snoc (bind σ A)) (.var .zero) T))
      (Telescope.lookup_lift_newest Γ A σ)).mpr
      (build (.variable (Δ.snoc (bind σ A)) .zero) (consEvidence D target (noEvidence D)))
  | succ v =>
    have old := renameEvidence (d.image v) (Δ.snoc (bind σ A))
      (Telescope.RawRen.projection (S := sig) .term m)
      (Telescope.RawRen.respects_projection Δ (bind σ A)) target
    have old' : D (typed (Δ.snoc (bind σ A)) (weaken (σ .term v))
        (weaken (bind σ (ContextGeometry.lookup Γ v)))) := by
      exact (congrArg₂ (fun t T => D (typed (Δ.snoc (bind σ A)) t T))
        (Telescope.bind_projection (S := sig) (b := .term) (σ .term v))
        (Telescope.bind_projection (S := sig) (b := .term) (bind σ (ContextGeometry.lookup Γ v)))).mp old
    exact (congrArg (fun T => D (typed (Δ.snoc (bind σ A)) (weaken (σ .term v)) T))
      (Telescope.lookup_lift_older Γ A v σ)).mpr old'

def SubstitutionAction (D : Judgment → Type) : Judgment → Type
  | .context ⟨n, Γ⟩ => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub n m),
      TypedSubstitution D Γ Δ σ → D (context Δ)
  | .type ⟨n, Γ⟩ A => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub n m),
      TypedSubstitution D Γ Δ σ → D (formed Δ (bind σ A))
  | .term ⟨n, Γ⟩ A t => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub n m),
      TypedSubstitution D Γ Δ σ → D (typed Δ (bind σ t.code) (bind σ A))
  | .typeEquality ⟨n, Γ⟩ A B => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub n m),
      TypedSubstitution D Γ Δ σ → D (typeEqual Δ (bind σ A) (bind σ B))
  | .termEquality ⟨n, Γ⟩ A t u => ∀ {m : Nat} (Δ : RawContext m) (σ : RawSub n m),
      TypedSubstitution D Γ Δ σ → D (termEqual Δ (bind σ t.code) (bind σ u.code) (bind σ A))
  | .substitution _ _ _ => Empty

private theorem bind_lift_projection {n m : Nat} (σ : RawSub n m) (t : RawTm n) :
    bind (Telescope.lift σ) (bind (Telescope.projection (S := sig) .term n) t) =
      bind (Telescope.projection (S := sig) .term m) (bind σ t) :=
  (TermBody.open_substitute σ (.noBind t)).symm

private theorem bind_lift_zero {n m : Nat} (σ : RawSub n m) :
    bind (Telescope.lift σ) (.var .zero : RawTm (n + 1)) =
      (.var .zero : RawTm (m + 1)) := rfl

/-- The static rules preserve substitution whose images have the required types. -/
def substituteRule
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    (renameEvidence : ∀ {j : Judgment}, D j → RenamingAction D j)
    {j : Judgment} (shape : RuleShape j)
    (children : Evidence D (premises shape))
    (ih : Evidence (SubstitutionAction D) (premises shape)) : SubstitutionAction D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let endChildren := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at children ih
  case empty => exact fun _ _ _ sub => sub.target
  case extend Γ A => exact fun _ _ _ sub => sub.target
  case formation Γ k a =>
    intro m Δ σ sub
    exact build (.formation Δ k (bind σ a)) (child (ih 0 Δ σ sub) endChildren)
  case sort Γ k =>
    intro m Δ σ sub
    exact build (.sort Δ k) (child sub.target endChildren)
  case «variable» Γ v =>
    intro m Δ σ sub
    exact sub.image v
  case pi Γ A B =>
    intro m Δ σ sub
    have da := ih 0 Δ σ sub
    have lifted := sub.lift algebra renameEvidence (children 0) da
    have db := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    simpa only [TypeBody.pi_substitute, TypeParameter.level_substitute, TypeBody.level_substitute,
      bind_universeCode] using build (.pi Δ (A.substitute σ) (B.substitute σ))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute] using db) endChildren))
  case lambda Γ A B body =>
    intro m Δ σ sub
    have da := ih 0 Δ σ sub
    have lifted := sub.lift algebra renameEvidence (children 0) da
    have db := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    have dt := ih 2 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    simpa only [TermBody.lambda_substitute, ← substitute_piType, TypeParameter.code_substitute] using
      build (.lambda Δ (A.substitute σ) (B.substitute σ) (body.substitute σ))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute] using db)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
            TermBody.open_substitute] using dt) endChildren)))
  case application Γ A B f a =>
    intro m Δ σ sub
    simpa only [TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.application Δ (A.substitute σ) (B.substitute σ) (bind σ f) (bind σ a))
        (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 0 Δ σ sub)
          (child (ih 1 Δ σ sub) endChildren))
  case conversion Γ t A B =>
    intro m Δ σ sub
    exact build (.conversion Δ (bind σ t) (bind σ A) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case typeEquality Γ k a b =>
    intro m Δ σ sub
    exact build (.typeEquality Δ k (bind σ a) (bind σ b))
      (child (ih 0 Δ σ sub) endChildren)
  case reflexivity Γ t A =>
    intro m Δ σ sub
    exact build (.reflexivity Δ (bind σ t) (bind σ A)) (child (ih 0 Δ σ sub) endChildren)
  case symmetry Γ t u A =>
    intro m Δ σ sub
    exact build (.symmetry Δ (bind σ t) (bind σ u) (bind σ A)) (child (ih 0 Δ σ sub) endChildren)
  case transitivity Γ t u v A =>
    intro m Δ σ sub
    exact build (.transitivity Δ (bind σ t) (bind σ u) (bind σ v) (bind σ A))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case equalityConversion Γ t u A B =>
    intro m Δ σ sub
    exact build (.equalityConversion Δ (bind σ t) (bind σ u) (bind σ A) (bind σ B))
      (child (ih 0 Δ σ sub) (child (ih 1 Δ σ sub) endChildren))
  case piCongruence Γ A A' B B' =>
    intro m Δ σ sub
    have da := ih 0 Δ σ sub
    have lifted := sub.lift algebra renameEvidence (children 0) da
    have db := ih 2 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    simpa only [TypeBody.pi_substitute, TypeParameter.level_substitute, TypeBody.level_substitute,
      bind_universeCode] using build (.piCongruence Δ (A.substitute σ) (A'.substitute σ)
        (B.substitute σ) (B'.substitute σ))
        (child da (child (ih 1 Δ σ sub)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute] using db) endChildren)))
  case applicationCongruence Γ A B f g a b =>
    intro m Δ σ sub
    simpa only [TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.applicationCongruence Δ (A.substitute σ) (B.substitute σ)
        (bind σ f) (bind σ g) (bind σ a) (bind σ b))
        (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 0 Δ σ sub)
          (child (ih 1 Δ σ sub) endChildren))
  case beta Γ A B body a =>
    intro m Δ σ sub
    have da := ih 0 Δ σ sub
    have lifted := sub.lift algebra renameEvidence (children 0) da
    have db := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    have dt := ih 2 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    simpa only [TermBody.lambda_substitute, TermBody.instantiate_substitute,
      TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.beta Δ (A.substitute σ) (B.substitute σ) (body.substitute σ) (bind σ a))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute] using db)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
            TermBody.open_substitute] using dt) (child (ih 3 Δ σ sub) endChildren))))
  case eta Γ A B f g =>
    intro m Δ σ sub
    have da := ih 0 Δ σ sub
    have lifted := sub.lift algebra renameEvidence (children 0) da
    have db := ih 1 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    have de := ih 4 (Δ.snoc (bind σ A.code)) (Telescope.lift σ) lifted
    simpa only [← substitute_piType, TypeParameter.code_substitute] using
      build (.eta Δ (A.substitute σ) (B.substitute σ) (bind σ f) (bind σ g))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute] using db)
          (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 2 Δ σ sub)
            (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 3 Δ σ sub)
              (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
                bind_app, bind_lift_projection, bind_lift_zero] using de) endChildren)))))

/-- Substitution recursively constructs trees in the original presentation. -/
noncomputable def Derivation.substitution {j : Judgment} (tree : Derivation j) : SubstitutionAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => SubstitutionAction Derivation j)
    (fun _ _ shape children ih => substituteRule
      (IndexedPolynomial.Algebra.initial presentation.polynomial) Derivation.renaming shape children ih)
    () j tree

end Mettapedia.Languages.Agda.Structural.Statics
