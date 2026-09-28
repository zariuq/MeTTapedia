import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityBasic

/-!
Validity transport through the semantic equivalence laws. In particular,
pointwise equality and left validity derive right validity, including its
action on unequal but semantically equal substitutions.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory

theorem ValidTypeEq.ofLeft {Γ : RawContext n} {A B : Ty n}
    (source : TypeEq Γ A B) (left : ValidType Γ A)
    (equal : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
      (annotatedPack Δ (A.subst σ)).eqTy (B.subst σ)) : ValidTypeEq Γ A B := by
  refine ⟨⟨source⟩, left, ?_, equal⟩
  refine ⟨⟨(typeEndpoints source).right⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    exact ((left.reducible substitution).typeEqualityCanonical (equal substitution)).1
  · intro m Δ σ τ substitution
    have leftRelated := left.reducible substitution.left
    have rightRelated := left.reducible substitution.right
    have leftBoundary := leftRelated.typeEqualityCanonical (equal substitution.left)
    have comparison := leftRelated.transitiveTypeEquality rightRelated
      (left.extension substitution) (equal substitution.right)
    rw [← leftBoundary.2]
    exact comparison

theorem ValidTermEq.ofLeft {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (source : TermEq Γ t u A) (left : ValidTerm Γ t A)
    (equal : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
      (annotatedPack Δ (A.subst σ)).eqTm (t.subst σ) (u.subst σ)) : ValidTermEq Γ t u A := by
  refine ⟨⟨source⟩, left, ?_, equal⟩
  refine ⟨⟨(termEndpoints source).right⟩, left.type, ?_, ?_⟩
  · intro m Δ σ substitution
    exact ((left.type.reducible substitution).equalityMembers (equal substitution)).2
  · intro m Δ σ τ substitution
    have leftRelated := left.type.reducible substitution.left
    have rightRelated := left.type.reducible substitution.right
    have same := leftRelated.convertPacks rightRelated (left.type.extension substitution)
    have atRight : (annotatedPack Δ (A.subst σ)).eqTm (t.subst τ) (u.subst τ) := by
      rw [same]
      exact equal substitution.right
    exact leftRelated.transitiveTermEquality
      (leftRelated.symmetricTermEquality (equal substitution.left))
      (leftRelated.transitiveTermEquality (left.extension substitution) atRight)

theorem ValidTerm.conv {Γ : RawContext n} {t : Term n} {A B : Ty n}
    (valid : ValidTerm Γ t A) (equal : ValidTypeEq Γ A B) : ValidTerm Γ t B := by
  obtain ⟨typed⟩ := valid.source
  obtain ⟨converted⟩ := equal.source
  refine ⟨⟨.conv typed converted⟩, equal.right, ?_, ?_⟩
  · intro m Δ σ substitution
    rw [← (equal.left.reducible substitution).convertPacks (equal.right.reducible substitution)
      (equal.equal substitution)]
    exact valid.member substitution
  · intro m Δ σ τ substitution
    rw [← (equal.left.reducible substitution.left).convertPacks (equal.right.reducible substitution.left)
      (equal.equal substitution.left)]
    exact valid.extension substitution

theorem ValidTermEq.refl {Γ : RawContext n} {t : Term n} {A : Ty n}
    (valid : ValidTerm Γ t A) : ValidTermEq Γ t t A := by
  obtain ⟨typed⟩ := valid.source
  exact ⟨⟨.refl typed⟩, valid, valid,
    fun substitution => (valid.type.reducible substitution).reflexive.term (valid.member substitution)⟩

theorem ValidTermEq.symm {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (valid : ValidTermEq Γ t u A) : ValidTermEq Γ u t A := by
  obtain ⟨source⟩ := valid.source
  exact ⟨⟨.symm source⟩, valid.right, valid.left,
    fun substitution => (valid.left.type.reducible substitution).symmetricTermEquality
      (valid.equal substitution)⟩

theorem ValidTermEq.trans {Γ : RawContext n} {t u v : Term n} {A : Ty n}
    (first : ValidTermEq Γ t u A) (second : ValidTermEq Γ u v A) : ValidTermEq Γ t v A := by
  obtain ⟨firstSource⟩ := first.source
  obtain ⟨secondSource⟩ := second.source
  exact ⟨⟨.trans firstSource secondSource⟩, first.left, second.right,
    fun substitution => (first.left.type.reducible substitution).transitiveTermEquality
      (first.equal substitution) (second.equal substitution)⟩

theorem ValidTermEq.conv {Γ : RawContext n} {t u : Term n} {A B : Ty n}
    (valid : ValidTermEq Γ t u A) (equal : ValidTypeEq Γ A B) : ValidTermEq Γ t u B := by
  obtain ⟨source⟩ := valid.source
  obtain ⟨converted⟩ := equal.source
  refine ⟨⟨.conv source converted⟩, valid.left.conv equal, valid.right.conv equal, ?_⟩
  intro m Δ σ substitution
  rw [← (equal.left.reducible substitution).convertPacks (equal.right.reducible substitution)
    (equal.equal substitution)]
  exact valid.equal substitution

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
