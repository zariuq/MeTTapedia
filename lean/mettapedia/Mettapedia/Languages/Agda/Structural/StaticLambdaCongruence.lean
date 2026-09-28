import Mettapedia.Languages.Agda.Structural.StaticEvidenceOperations

/-!
# Lambda congruence derived from typed beta and eta

Binding and nonbinding abstractions are compared by opening them in the same
formed extended context. Pointwise beta uses the generic lift and single
substitution; eta then closes the equality. Both body typing trees are retained
as premises. No lambda-congruence axiom or extra typing rule is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

private theorem liftedProjection_single (n : Nat) :
    Telescope.comp (Telescope.lift (Telescope.projection (S := sig) .term n))
      (single (.var .zero : RawTm (n + 1))) = Telescope.identity (S := sig) .term (n + 1) := by
  funext s v
  cases v <;> rfl

theorem TermBody.instantiate_projected_newest {n : Nat} (body : TermBody n) :
    (body.substitute (Telescope.projection (S := sig) .term n)).instantiate (.var .zero) = body.open := by
  unfold TermBody.instantiate
  rw [TermBody.open_substitute]
  exact (Telescope.bind_compose _ _ body.open).trans
    ((congrArg (fun σ => Mettapedia.OSLF.Binding.bind σ body.open) (liftedProjection_single n)).trans
      (Telescope.bind_identity body.open))

theorem TypeBody.instantiate_projected_newest {n : Nat} (body : TypeBody n) :
    (body.substitute (Telescope.projection (S := sig) .term n)).instantiate (.var .zero) = body.open := by
  unfold TypeBody.instantiate
  rw [TypeBody.open_substitute]
  exact (TypeParameter.substitute_comp body.open _ _).trans
    ((congrArg (fun σ => body.open.substitute σ) (liftedProjection_single n)).trans
      (TypeParameter.substitute_identity body.open))

namespace EvidenceOperations

variable {D : Judgment → Type} (ops : EvidenceOperations D)

def betaAtNewest {n : Nat} {Γ : RawContext n} {A : TypeParameter n}
    {B : TypeBody n} {body : TermBody n}
    (domain : D (formed Γ A.code)) (codomain : D (formed (Γ.snoc A.code) B.open.code))
    (typedBody : D (typed (Γ.snoc A.code) body.open B.open.code)) :
    D (termEqual (Γ.snoc A.code)
      (app (bind (Telescope.projection (S := sig) .term n) body.lambda) (.var .zero))
      body.open B.open.code) := by
  let ρ := Telescope.RawRen.projection (S := sig) .term n
  have target := ops.extend (ops.contexts domain) domain
  have respects := Telescope.RawRen.respects_projection Γ A.code
  have da := ops.renameEvidence domain (Γ.snoc A.code) ρ respects target
  have liftedTarget := ops.extend target da
  have db := ops.renameEvidence codomain ((Γ.snoc A.code).snoc (bind ρ.asSub A.code))
    ρ.lift (respects.lift A.code) liftedTarget
  have dt := ops.renameEvidence typedBody ((Γ.snoc A.code).snoc (bind ρ.asSub A.code))
    ρ.lift (respects.lift A.code) liftedTarget
  have dx := ops.build (.variable (Γ.snoc A.code) .zero) (consEvidence D target (noEvidence D))
  have dx' : D (typed (Γ.snoc A.code) (.var .zero) (A.substitute ρ.asSub).code) :=
    (congrArg (fun T => D (typed (Γ.snoc A.code) (.var .zero) T))
      (Telescope.bind_projection (S := sig) (b := .term) A.code)).mpr dx
  have beta := ops.build (.beta (Γ.snoc A.code) (A.substitute ρ.asSub)
    (B.substitute ρ.asSub) (body.substitute ρ.asSub) (.var .zero))
    (consEvidence D da
      (consEvidence D (by simpa only [TypeBody.open_substitute, TypeParameter.code_substitute,
        Telescope.RawRen.asSub_lift ρ] using db)
        (consEvidence D (by simpa only [TermBody.open_substitute, TypeBody.open_substitute,
          TypeParameter.code_substitute, Telescope.RawRen.asSub_lift ρ] using dt)
          (consEvidence D dx' (noEvidence D)))))
  change D (termEqual (Γ.snoc A.code)
    (app ((body.substitute (Telescope.projection (S := sig) .term n)).lambda) (.var .zero))
    ((body.substitute (Telescope.projection (S := sig) .term n)).instantiate (.var .zero))
    ((B.substitute (Telescope.projection (S := sig) .term n)).instantiate (.var .zero)).code) at beta
  simpa only [TermBody.lambda_substitute, TermBody.instantiate_projected_newest,
    TypeBody.instantiate_projected_newest] using beta

def lambdaCongruence {n : Nat} {Γ : RawContext n} {A : TypeParameter n}
    {B : TypeBody n} {first second : TermBody n}
    (domain : D (formed Γ A.code)) (codomain : D (formed (Γ.snoc A.code) B.open.code))
    (firstTyped : D (typed (Γ.snoc A.code) first.open B.open.code))
    (secondTyped : D (typed (Γ.snoc A.code) second.open B.open.code))
    (bodies : D (termEqual (Γ.snoc A.code) first.open second.open B.open.code)) :
    D (termEqual Γ first.lambda second.lambda (piType A B).code) := by
  let child := @consEvidence _ D
  let stop := noEvidence D
  have firstLambda := ops.build (.lambda Γ A B first) (child domain (child codomain (child firstTyped stop)))
  have secondLambda := ops.build (.lambda Γ A B second) (child domain (child codomain (child secondTyped stop)))
  have firstBeta := ops.betaAtNewest domain codomain firstTyped
  have secondBeta := ops.betaAtNewest domain codomain secondTyped
  let left := app (bind (Telescope.projection (S := sig) .term n) first.lambda) (.var .zero)
  let right := app (bind (Telescope.projection (S := sig) .term n) second.lambda) (.var .zero)
  have secondInverse := ops.build (.symmetry (Γ.snoc A.code) right second.open B.open.code)
    (child secondBeta stop)
  have middle := ops.build (.transitivity (Γ.snoc A.code) first.open second.open right B.open.code)
    (child bodies (child secondInverse stop))
  have pointwise := ops.build (.transitivity (Γ.snoc A.code) left first.open right B.open.code)
    (child firstBeta (child middle stop))
  exact ops.build (.eta Γ A B first.lambda second.lambda)
    (child domain (child codomain (child firstLambda (child secondLambda (child pointwise stop)))))

end EvidenceOperations

end Mettapedia.Languages.Agda.Structural.Statics
