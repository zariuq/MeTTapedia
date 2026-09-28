import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropLift

/-!
Exact source annotations give a uniform sufficient semantic bound. This
eliminates arbitrary existential bounds from the subsequent validity layer;
it changes no source type or derivation and does not assert cumulativity.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

@[simp] theorem instantiate_level (B : TyAbs n) (a : Term n) :
    (B.instantiate a).level = B.level := by
  simp only [TyAbs.instantiate, Ty.level_subst, TyAbs.level_open]

theorem LogRel.atAnnotation {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) : LogRel A.level Γ A P := by
  induction related with
  | @«universe» n Γ A k less red =>
      obtain ⟨red⟩ := red
      have sufficient : k < A.level := by
        rw [red.level]
        exact Nat.lt_succ_self k
      have small : LogRel A.level Γ A (universePack (below A.level) Γ k) :=
        LR.universe sufficient ⟨red⟩
      have original : LogRel bound Γ A (universePack (below bound) Γ k) :=
        LR.universe less ⟨red⟩
      exact original.irrelevantAcross small ▸ small
  | neutral red normal => exact .neutral red normal
  | @pi n Γ A domain codomain red formedDomain formedCodomain family _ _ domainsIH codomainsIH =>
      obtain ⟨red⟩ := red
      have domainLe : domain.level ≤ A.level := by
        rw [red.level]
        exact Nat.le_max_left _ _
      have codomainLe : codomain.level ≤ A.level := by
        rw [red.level]
        exact Nat.le_max_right _ _
      refine LR.pi ⟨red⟩ formedDomain formedCodomain family ?_ ?_
      · intro m Δ ρ world
        exact LogRel.raise (by simpa only [Ty.level_rename] using domainLe) (domainsIH world)
      · intro m Δ ρ world a argument
        exact LogRel.raise (by simpa only [instantiate_level, TyAbs.level_rename] using codomainLe)
          (codomainsIH world argument)

/-- At an annotated type, existence at some bound is exactly existence at its
own level. The canonical predicate pack is therefore named without a bound. -/
def annotatedPack (Γ : RawContext n) (A : Ty n) : Pack n := canonicalPack A.level Γ A

theorem LogRel.annotatedPack_eq {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) : annotatedPack Γ A = P :=
  related.atAnnotation.canonicalPack_eq

theorem LogRel.annotated {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) : LogRel A.level Γ A (annotatedPack Γ A) := by
  rw [related.annotatedPack_eq]
  exact related.atAnnotation

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
