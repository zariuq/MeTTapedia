import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropCoherence

/-!
Increasing the semantic bound preserves the same predicates. This is a law
of the finite semantic table; source type annotations and typing derivations
are unchanged, and no cumulative source rule is introduced.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification

private theorem universePack_congr {lower upper : Nat → Relation} {k : Nat}
    (same : ∀ {n : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n},
      lower k Γ A P ↔ upper k Γ A P) (Γ : RawContext n) :
    universePack lower Γ k = universePack upper Γ k := by
  have equal : @lower k = @upper k := by
    funext n Δ A P
    exact propext same
  unfold universePack
  rw [equal]

theorem LR.raise {bound larger : Nat} {lower upper : Nat → Relation}
    (increase : bound ≤ larger)
    (sameBelow : ∀ {k : Nat}, k < bound →
      ∀ {n : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n},
        lower k Γ A P ↔ upper k Γ A P)
    {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LR bound lower Γ A P) : LR larger upper Γ A P := by
  induction related with
  | «universe» less red =>
      rw [universePack_congr (sameBelow less)]
      exact .universe (Nat.lt_of_lt_of_le less increase) red
  | neutral red normal => exact .neutral red normal
  | pi red domain codomain family _ _ domainsIH codomainsIH =>
      exact .pi red domain codomain family domainsIH codomainsIH

theorem LogRel.raise {bound larger : Nat} (increase : bound ≤ larger)
    {Γ : RawContext n} {A : Ty n} {P : Pack n} (related : LogRel bound Γ A P) :
    LogRel larger Γ A P := by
  refine LR.raise increase ?_ related
  intro k less n Δ B Q
  exact (below_iff less).trans (below_iff (Nat.lt_of_lt_of_le less increase)).symm

/-- Predicate coherence also holds when witnesses use different bounds. -/
theorem LogRel.irrelevantAcross {leftBound rightBound : Nat} {Γ : RawContext n}
    {A : Ty n} {P Q : Pack n} (left : LogRel leftBound Γ A P)
    (right : LogRel rightBound Γ A Q) : P = Q :=
  (LogRel.raise (Nat.le_max_left leftBound rightBound) left).irrelevant
    (LogRel.raise (Nat.le_max_right leftBound rightBound) right)

theorem canonicalPack_stable {leftBound rightBound : Nat} {Γ : RawContext n} {A : Ty n}
    (leftExists : ∃ P, LogRel leftBound Γ A P)
    (rightExists : ∃ Q, LogRel rightBound Γ A Q) :
    canonicalPack leftBound Γ A = canonicalPack rightBound Γ A :=
  (canonicalPack_related leftExists).irrelevantAcross (canonicalPack_related rightExists)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
