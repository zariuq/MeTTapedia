import Mettapedia.Languages.Agda.Structural.StaticSubstitution
import Mettapedia.Languages.Agda.Structural.StaticConstructors
import Mettapedia.OSLF.Syntax.BindingTelescopeRenaming

/-!
# Renaming actual static rule trees

The rule-by-rule algebra below transforms ordered premise evidence. It is
parametric in the target algebra, so extensions of the static presentation can
reuse it without replacing their recursive evidence by canonical-only trees.
The variable boundary requires compatible telescope lookups and a formed
target context. No arbitrary raw substitution is declared type preserving.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

abbrev RawRen (n m : Nat) := Telescope.RawRen sig .term n m

/-- The action required of a judgment under declaration-respecting renaming. -/
def RenamingAction (D : Judgment → Type) : Judgment → Type
  | .context ⟨n, Γ⟩ => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen n m),
      ρ.Respects Γ Δ → D (context Δ) → D (context Δ)
  | .type ⟨n, Γ⟩ A => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen n m),
      ρ.Respects Γ Δ → D (context Δ) → D (formed Δ (bind ρ.asSub A))
  | .term ⟨n, Γ⟩ A t => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen n m),
      ρ.Respects Γ Δ → D (context Δ) → D (typed Δ (bind ρ.asSub t.code) (bind ρ.asSub A))
  | .typeEquality ⟨n, Γ⟩ A B => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen n m),
      ρ.Respects Γ Δ → D (context Δ) → D (typeEqual Δ (bind ρ.asSub A) (bind ρ.asSub B))
  | .termEquality ⟨n, Γ⟩ A t u => ∀ {m : Nat} (Δ : RawContext m) (ρ : RawRen n m),
      ρ.Respects Γ Δ → D (context Δ) →
        D (termEqual Δ (bind ρ.asSub t.code) (bind ρ.asSub u.code) (bind ρ.asSub A))
  | .substitution _ _ _ => Empty

private theorem bind_lift_projection {n m : Nat} (σ : RawSub n m) (t : RawTm n) :
    bind (Telescope.lift σ) (bind (Telescope.projection (S := sig) .term n) t) =
      bind (Telescope.projection (S := sig) .term m) (bind σ t) :=
  (TermBody.open_substitute σ (.noBind t)).symm

private theorem bind_lift_zero {n m : Nat} (σ : RawSub n m) :
    bind (Telescope.lift σ) (.var .zero : RawTm (n + 1)) =
      (.var .zero : RawTm (m + 1)) := rfl

/-- Interpret a canonical constructor using the transformed children. -/
def renameRule {D : Judgment → Type}
    (algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j))
    {j : Judgment} (shape : RuleShape j)
    (ih : Evidence (RenamingAction D) (premises shape)) : RenamingAction D j := by
  let build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
    algebra.act () j ⟨shape, children⟩
  let endChildren := noEvidence D
  let child := @consEvidence _ D
  cases shape <;> simp only [premises] at ih
  case empty => exact fun _ _ _ _ target => target
  case extend Γ A => exact fun _ _ _ _ target => target
  case formation Γ k a =>
    intro m Δ ρ respects target
    exact build (.formation Δ k (bind ρ.asSub a)) (child (ih 0 Δ ρ respects target) endChildren)
  case sort Γ k =>
    intro m Δ ρ respects target
    exact build (.sort Δ k) (child target endChildren)
  case «variable» Γ v =>
    intro m Δ ρ respects target
    exact (congrArg (fun A => D (typed Δ (.var (ρ .term v)) A)) (respects v)).mp
      (build (.variable Δ (ρ .term v)) (child target endChildren))
  case pi Γ A B =>
    intro m Δ ρ respects target
    have da := ih 0 Δ ρ respects target
    have extended := build (.extend Δ (bind ρ.asSub A.code)) (child target (child da endChildren))
    have db := ih 1 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    simpa only [TypeBody.pi_substitute, TypeParameter.code_substitute, TypeParameter.level_substitute,
      TypeBody.level_substitute, bind_universeCode] using build (.pi Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub))
      (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
        Telescope.RawRen.asSub_lift ρ] using db) endChildren))
  case lambda Γ A B body =>
    intro m Δ ρ respects target
    have da := ih 0 Δ ρ respects target
    have extended := build (.extend Δ (bind ρ.asSub A.code)) (child target (child da endChildren))
    have db := ih 1 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    have dt := ih 2 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    simpa only [TermBody.lambda_substitute, ← substitute_piType, TypeParameter.code_substitute] using
      build (.lambda Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub) (body.substitute ρ.asSub))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
          Telescope.RawRen.asSub_lift ρ] using db)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
            TermBody.open_substitute, Telescope.RawRen.asSub_lift ρ] using dt) endChildren)))
  case application Γ A B f a =>
    intro m Δ ρ respects target
    simpa only [TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.application Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub)
        (bind ρ.asSub f) (bind ρ.asSub a))
        (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 0 Δ ρ respects target)
          (child (ih 1 Δ ρ respects target) endChildren))
  case conversion Γ t A B =>
    intro m Δ ρ respects target
    exact build (.conversion Δ (bind ρ.asSub t) (bind ρ.asSub A) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case typeEquality Γ k a b =>
    intro m Δ ρ respects target
    exact build (.typeEquality Δ k (bind ρ.asSub a) (bind ρ.asSub b))
      (child (ih 0 Δ ρ respects target) endChildren)
  case reflexivity Γ t A =>
    intro m Δ ρ respects target
    exact build (.reflexivity Δ (bind ρ.asSub t) (bind ρ.asSub A))
      (child (ih 0 Δ ρ respects target) endChildren)
  case symmetry Γ t u A =>
    intro m Δ ρ respects target
    exact build (.symmetry Δ (bind ρ.asSub t) (bind ρ.asSub u) (bind ρ.asSub A))
      (child (ih 0 Δ ρ respects target) endChildren)
  case transitivity Γ t u v A =>
    intro m Δ ρ respects target
    exact build (.transitivity Δ (bind ρ.asSub t) (bind ρ.asSub u) (bind ρ.asSub v) (bind ρ.asSub A))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case equalityConversion Γ t u A B =>
    intro m Δ ρ respects target
    exact build (.equalityConversion Δ (bind ρ.asSub t) (bind ρ.asSub u) (bind ρ.asSub A) (bind ρ.asSub B))
      (child (ih 0 Δ ρ respects target) (child (ih 1 Δ ρ respects target) endChildren))
  case piCongruence Γ A A' B B' =>
    intro m Δ ρ respects target
    have da := ih 0 Δ ρ respects target
    have extended := build (.extend Δ (bind ρ.asSub A.code)) (child target (child da endChildren))
    have db := ih 2 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    simpa only [TypeBody.pi_substitute, TypeParameter.level_substitute, TypeBody.level_substitute,
      bind_universeCode] using
      build (.piCongruence Δ (A.substitute ρ.asSub) (A'.substitute ρ.asSub)
        (B.substitute ρ.asSub) (B'.substitute ρ.asSub))
        (child da (child (ih 1 Δ ρ respects target)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
            Telescope.RawRen.asSub_lift ρ] using db) endChildren)))
  case applicationCongruence Γ A B f g a b =>
    intro m Δ ρ respects target
    simpa only [TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.applicationCongruence Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub)
        (bind ρ.asSub f) (bind ρ.asSub g) (bind ρ.asSub a) (bind ρ.asSub b))
        (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 0 Δ ρ respects target)
          (child (ih 1 Δ ρ respects target) endChildren))
  case beta Γ A B body a =>
    intro m Δ ρ respects target
    have da := ih 0 Δ ρ respects target
    have extended := build (.extend Δ (bind ρ.asSub A.code)) (child target (child da endChildren))
    have db := ih 1 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    have dt := ih 2 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    simpa only [TermBody.lambda_substitute, TermBody.instantiate_substitute,
      TypeBody.instantiate_substitute, TypeParameter.code_substitute, bind_app] using
      build (.beta Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub)
        (body.substitute ρ.asSub) (bind ρ.asSub a))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
          Telescope.RawRen.asSub_lift ρ] using db)
          (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
            TermBody.open_substitute, Telescope.RawRen.asSub_lift ρ] using dt)
            (child (ih 3 Δ ρ respects target) endChildren))))
  case eta Γ A B f g =>
    intro m Δ ρ respects target
    have da := ih 0 Δ ρ respects target
    have extended := build (.extend Δ (bind ρ.asSub A.code)) (child target (child da endChildren))
    have db := ih 1 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    have de := ih 4 (Δ.snoc (bind ρ.asSub A.code)) ρ.lift (respects.lift A.code) extended
    simpa only [← substitute_piType, TypeParameter.code_substitute] using
      build (.eta Δ (A.substitute ρ.asSub) (B.substitute ρ.asSub) (bind ρ.asSub f) (bind ρ.asSub g))
        (child da (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
          Telescope.RawRen.asSub_lift ρ] using db)
          (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 2 Δ ρ respects target)
            (child (by simpa only [← substitute_piType, TypeParameter.code_substitute] using ih 3 Δ ρ respects target)
              (child (by simpa only [TypeParameter.code_substitute, TypeBody.open_substitute,
                Telescope.RawRen.asSub_lift ρ, bind_app, bind_lift_projection, bind_lift_zero] using de) endChildren)))))

/-- Every canonical static tree admits declaration-respecting renaming. -/
noncomputable def Derivation.renaming {j : Judgment} (tree : Derivation j) : RenamingAction Derivation j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => RenamingAction Derivation j)
    (fun _ _ shape _children ih => renameRule (IndexedPolynomial.Algebra.initial presentation.polynomial) shape ih)
    () j tree

end Mettapedia.Languages.Agda.Structural.Statics
