import Mettapedia.Languages.Agda.Structural.StaticEvidenceOperations

/-!
# Pointwise equality of typed structural substitutions

Both substitutions retain context and variable-image derivations. Their images
are compared at the left substituted lookup type. Lifting consequently keeps
the left extended target context and converts the right newest image. These
are evidence transformations, not equations identifying derivation histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

structure EqualSubstitution (D : Judgment → Type) {n m : Nat}
    (Γ : RawContext n) (Δ : RawContext m) (σ τ : RawSub n m) where
  left : TypedSubstitution D Γ Δ σ
  right : TypedSubstitution D Γ Δ τ
  equal : (v : Var (scope n) .term) →
    D (termEqual Δ (σ .term v) (τ .term v) (bind σ (ContextGeometry.lookup Γ v)))

variable {D : Judgment → Type}

def EqualSubstitution.lift (ops : EvidenceOperations D)
    {n m : Nat} {Γ : RawContext n} {Δ : RawContext m} {σ τ : RawSub n m}
    (sub : EqualSubstitution D Γ Δ σ τ) {A : RawTy n}
    (domain : D (formed Γ A)) (domains : D (typeEqual Δ (bind σ A) (bind τ A))) :
    EqualSubstitution D (Γ.snoc A) (Δ.snoc (bind σ A)) (Telescope.lift σ) (Telescope.lift τ) := by
  let imageDomain := ops.substituteEvidence domain Δ σ sub.left
  let left := sub.left.lift ops.algebra ops.renameEvidence domain imageDomain
  let target := left.target
  let renameOlder {j : Judgment} (tree : D j) := ops.renameEvidence tree
  refine ⟨left, ⟨left.source, target, ?_⟩, ?_⟩
  · intro v
    cases v with
    | zero =>
      have newest := ops.build (.variable (Δ.snoc (bind σ A)) .zero) (consEvidence D target (noEvidence D))
      have converted := ops.build (.conversion (Δ.snoc (bind σ A)) (.var .zero)
        (weaken (bind σ A)) (weaken (bind τ A)))
        (consEvidence D newest
          (consEvidence D (ops.weakenTypeEquality imageDomain domains) (noEvidence D)))
      exact (congrArg (fun T => D (typed (Δ.snoc (bind σ A)) (.var .zero) T))
        (Telescope.lookup_lift_newest Γ A τ)).mpr converted
    | succ v =>
      have older := renameOlder (sub.right.image v) (Δ.snoc (bind σ A))
        (Telescope.RawRen.projection (S := sig) .term m)
        (Telescope.RawRen.respects_projection Δ (bind σ A)) target
      have weaker := (congrArg₂ (fun t T => D (typed (Δ.snoc (bind σ A)) t T))
        (Telescope.bind_projection (S := sig) (b := .term) (τ .term v))
        (Telescope.bind_projection (S := sig) (b := .term) (bind τ (ContextGeometry.lookup Γ v)))).mp older
      exact (congrArg (fun T => D (typed (Δ.snoc (bind σ A)) (weaken (τ .term v)) T))
        (Telescope.lookup_lift_older Γ A v τ)).mpr weaker
  · intro v
    cases v with
    | zero =>
      have newest := ops.build (.variable (Δ.snoc (bind σ A)) .zero) (consEvidence D target (noEvidence D))
      have reflexive := ops.build (.reflexivity (Δ.snoc (bind σ A)) (.var .zero) (weaken (bind σ A)))
        (consEvidence D newest (noEvidence D))
      exact (congrArg (fun T => D (termEqual (Δ.snoc (bind σ A)) (.var .zero) (.var .zero) T))
        (Telescope.lookup_lift_newest Γ A σ)).mpr reflexive
    | succ v =>
      have older := renameOlder (sub.equal v) (Δ.snoc (bind σ A))
        (Telescope.RawRen.projection (S := sig) .term m)
        (Telescope.RawRen.respects_projection Δ (bind σ A)) target
      have weaker : D (termEqual (Δ.snoc (bind σ A)) (weaken (σ .term v)) (weaken (τ .term v))
          (weaken (bind σ (ContextGeometry.lookup Γ v)))) := by
        have terms := congrArg₂ Prod.mk
          (Telescope.bind_projection (S := sig) (b := .term) (σ .term v))
          (Telescope.bind_projection (S := sig) (b := .term) (τ .term v))
        have boundary := congrArg₂ (fun (pair : RawTm (m + 1) × RawTm (m + 1)) T =>
          D (termEqual (Δ.snoc (bind σ A)) pair.1 pair.2 T)) terms
          (Telescope.bind_projection (S := sig) (b := .term) (bind σ (ContextGeometry.lookup Γ v)))
        exact boundary.mp older
      exact (congrArg (fun T => D (termEqual (Δ.snoc (bind σ A))
        (weaken (σ .term v)) (weaken (τ .term v)) T))
        (Telescope.lookup_lift_older Γ A v σ)).mpr weaker

def EqualSubstitution.single (ops : EvidenceOperations D)
    {n : Nat} {Γ : RawContext n} {A : RawTy n} {u v : RawTm n}
    (domain : D (formed Γ A)) (left : D (typed Γ u A)) (right : D (typed Γ v A))
    (equal : D (termEqual Γ u v A)) : EqualSubstitution D (Γ.snoc A) Γ (Statics.single u) (Statics.single v) where
  left := ops.singleSubstitution domain left
  right := ops.singleSubstitution domain right
  equal index := by
    cases index with
    | zero =>
      exact (congrArg (fun T => D (termEqual Γ u v T))
        ((Telescope.lookup_pair_newest Γ A (Telescope.identity (S := sig) .term n) u).trans
          (Telescope.bind_identity A))).mpr equal
    | succ index =>
      have typed := ops.build (.variable Γ index) (consEvidence D (ops.contexts domain) (noEvidence D))
      have reflexive := ops.build (.reflexivity Γ (.var index) (ContextGeometry.lookup Γ index))
        (consEvidence D typed (noEvidence D))
      exact (congrArg (fun T => D (termEqual Γ (.var index) (.var index) T))
        ((Telescope.lookup_pair_older Γ A index (Telescope.identity (S := sig) .term n) u).trans
          (Telescope.bind_identity (ContextGeometry.lookup Γ index)))).mpr reflexive

end Mettapedia.Languages.Agda.Structural.Statics
