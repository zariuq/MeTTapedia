import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropPiParts

/-!
Coherence of semantic packs over the same raw source type. Determinism of
raw weak-head reduction separates the three clauses; the positive relation
induction compares every Pi domain and every instantiated codomain. The
canonical pack below is formed from predicates, without selecting a witness
from a proposition into Type.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

private theorem typeRed_unique {Γ : RawContext n} {A B C : Ty n}
    (first : TypeRed Γ A B) (second : TypeRed Γ A C)
    (left : Whnf B.term) (right : Whnf C.term) : B = C := by
  have terms := first.steps.raw.normal_unique second.steps.raw left right
  have levels := first.level.symm.trans second.level
  cases B with
  | el k b =>
      cases C with
      | el l c =>
          cases levels
          cases terms
          rfl

theorem LR.irrelevant {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P Q : Pack n} (left : LR bound lower Γ A P)
    (right : LR bound lower Γ A Q) : P = Q := by
  induction left with
  | «universe» _ first =>
      obtain ⟨first⟩ := first
      cases right with
      | «universe» _ second =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.sort _) (.sort _)
          cases same
          rfl
      | neutral second neutral =>
          obtain ⟨second⟩ := second
          obtain ⟨neutral⟩ := neutral
          have same := first.steps.raw.normal_unique second.steps.raw (.sort _) (.neutral neutral)
          have impossible : Neutral (.sort _) := same.symm ▸ neutral
          cases impossible
      | pi second _ _ _ _ _ =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.sort _) (.pi _ _)
          cases same
  | neutral first normal =>
      obtain ⟨first⟩ := first
      obtain ⟨normal⟩ := normal
      cases right with
      | «universe» _ second =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.neutral normal) (.sort _)
          have impossible : Neutral (.sort _) := same ▸ normal
          cases impossible
      | neutral second normal' =>
          obtain ⟨second⟩ := second
          obtain ⟨normal'⟩ := normal'
          have same := typeRed_unique first second (.neutral normal) (.neutral normal')
          cases same
          rfl
      | pi second _ _ _ _ _ =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.neutral normal) (.pi _ _)
          have impossible : Neutral (.pi _ _) := same ▸ normal
          cases impossible
  | pi first _ _ family _ _ domainsIH codomainsIH =>
      obtain ⟨first⟩ := first
      cases right with
      | «universe» _ second =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.pi _ _) (.sort _)
          cases same
      | neutral second normal =>
          obtain ⟨second⟩ := second
          obtain ⟨normal⟩ := normal
          have same := first.steps.raw.normal_unique second.steps.raw (.pi _ _) (.neutral normal)
          have impossible : Neutral (.pi _ _) := same.symm ▸ normal
          cases impossible
      | pi second _ _ family' domains' codomains' =>
          obtain ⟨second⟩ := second
          have same := first.steps.raw.normal_unique second.steps.raw (.pi _ _) (.pi _ _)
          obtain ⟨rfl, rfl⟩ := Term.pi.inj same
          have domainEq : @family.domain = @family'.domain := by
            funext m Δ ρ world
            exact domainsIH world (domains' world)
          have familyEq : family = family' := by
            cases family with
            | mk domain codomain extension =>
                cases family' with
                | mk domain' codomain' extension' =>
                    dsimp only at domainEq
                    cases domainEq
                    have codomainEq : @codomain = @codomain' := by
                      funext m Δ ρ world a argument
                      exact codomainsIH world argument (codomains' world argument)
                    cases codomainEq
                    rfl
          cases familyEq
          rfl

theorem LogRel.irrelevant {bound : Nat} {Γ : RawContext n} {A : Ty n}
    {P Q : Pack n} (left : LogRel bound Γ A P) (right : LogRel bound Γ A Q) : P = Q :=
  LR.irrelevant left right

/-- Predicate union is a concrete pack even when no related pack exists. -/
def canonicalPack (bound : Nat) (Γ : RawContext n) (A : Ty n) : Pack n where
  eqTy B := ∃ P, LogRel bound Γ A P ∧ P.eqTy B
  redTm t := ∃ P, LogRel bound Γ A P ∧ P.redTm t
  eqTm t u := ∃ P, LogRel bound Γ A P ∧ P.eqTm t u

private theorem pack_ext {P Q : Pack n} (types : P.eqTy = Q.eqTy)
    (terms : P.redTm = Q.redTm) (equalities : P.eqTm = Q.eqTm) : P = Q := by
  cases P
  cases Q
  cases types
  cases terms
  cases equalities
  rfl

theorem LogRel.canonicalPack_eq {bound : Nat} {Γ : RawContext n} {A : Ty n}
    {P : Pack n} (related : LogRel bound Γ A P) : canonicalPack bound Γ A = P := by
  cases P with
  | mk eqTy redTm eqTm =>
      apply pack_ext
      · funext B
        apply propext
        constructor
        · rintro ⟨Q, relatedQ, equal⟩
          cases related.irrelevant relatedQ
          exact equal
        · intro equal
          exact ⟨_, related, equal⟩
      · funext t
        apply propext
        constructor
        · rintro ⟨Q, relatedQ, member⟩
          cases related.irrelevant relatedQ
          exact member
        · intro member
          exact ⟨_, related, member⟩
      · funext t u
        apply propext
        constructor
        · rintro ⟨Q, relatedQ, equal⟩
          cases related.irrelevant relatedQ
          exact equal
        · intro equal
          exact ⟨_, related, equal⟩

theorem canonicalPack_related {bound : Nat} {Γ : RawContext n} {A : Ty n}
    (existsPack : ∃ P, LogRel bound Γ A P) :
    LogRel bound Γ A (canonicalPack bound Γ A) := by
  obtain ⟨P, related⟩ := existsPack
  rw [related.canonicalPack_eq]
  exact related

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
