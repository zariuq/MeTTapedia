import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropPacks

/-!
An ordinary positive inductive relation indexed by its semantic pack. Pi
components range over every formed renaming world. Universe clauses refer
strictly downward in a separate primitive-recursive finite level table.
The semantic bound is not a source cumulativity rule: exact Ty annotations
and every source typing premise remain unchanged.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

inductive LR (bound : Nat) (lower : Nat → Relation) :
    {n : Nat} → RawContext n → Ty n → Pack n → Prop
  | universe {Γ : RawContext n} {A : Ty n} {k : Nat} :
      k < bound → Nonempty (TypeRed Γ A (Ty.universe k)) →
      LR bound lower Γ A (universePack lower Γ k)
  | neutral {Γ : RawContext n} {A B : Ty n} :
      Nonempty (TypeRed Γ A B) → Nonempty (Neutral B.term) →
      LR bound lower Γ A (neutralPack Γ B)
  | pi {Γ : RawContext n} {A domain : Ty n} {codomain : TyAbs n}
      (red : Nonempty (TypeRed Γ A (Ty.pi domain codomain)))
      (domainFormed : Nonempty (FormTy Γ domain))
      (codomainFormed : Nonempty (FormTy (Γ.snoc domain) codomain.open))
      (family : PiFamily Γ domain codomain)
      (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ),
        LR bound lower Δ (domain.rename ρ) (family.domain w))
      (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
        {a : Term m} (argument : (family.domain w).redTm a),
        LR bound lower Δ ((codomain.rename ρ).instantiate a) (family.codomain w argument)) :
      LR bound lower Γ A (piPack Γ domain codomain family)

/-- A finite table: position k is installed exactly at the next stratum. -/
def below : Nat → Nat → Relation
  | 0 => fun _ {_n} _ _ _ => False
  | bound + 1 => fun k => if k = bound then LR bound (below bound) else below bound k

def LogRel (bound : Nat) : Relation := LR bound (below bound)

theorem below_iff {bound k : Nat} (less : k < bound) {Γ : RawContext n} {A : Ty n}
    {P : Pack n} : below bound k Γ A P ↔ LogRel k Γ A P := by
  induction bound with
  | zero => exact False.elim (Nat.not_lt_zero k less)
  | succ bound ih =>
      by_cases equal : k = bound
      · subst k; simp [below, LogRel]
      · have smaller : k < bound := by omega
        simpa only [below, if_neg equal] using ih smaller

theorem below_empty {bound k : Nat} (outside : bound ≤ k) {Γ : RawContext n} {A : Ty n}
    {P : Pack n} : ¬ below bound k Γ A P := by
  induction bound with
  | zero => exact id
  | succ bound ih =>
      have different : k ≠ bound := by omega
      simpa only [below, if_neg different] using ih (by omega)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
