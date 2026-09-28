import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropEscape

/-! Reflexivity is derived by positive relation induction and finite level induction. -/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure Reflexive (A : Ty n) (P : Pack n) : Prop where
  type : P.eqTy A
  term : ∀ {t}, P.redTm t → P.eqTm t t

def LowerReflexive (bound : Nat) (lower : Nat → Relation) : Prop :=
  ∀ {k : Nat}, k < bound → ∀ {n : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n},
    lower k Γ A P → Reflexive A P

theorem LR.reflexive {bound : Nat} {lower : Nat → Relation}
    (lowerReflexive : LowerReflexive bound lower) {Γ : RawContext n} {A : Ty n}
    {P : Pack n} (related : LR bound lower Γ A P) : Reflexive A P := by
  induction related with
  | «universe» less red =>
      refine ⟨red, ?_⟩
      rintro t ⟨nf, ⟨path⟩, normal, Q, relatedQ⟩
      exact ⟨nf, nf, ⟨path⟩, ⟨path⟩, normal, normal,
        ⟨.refl path.endpoints.right⟩, ⟨Q, relatedQ⟩, Q, relatedQ,
        (lowerReflexive less relatedQ).type⟩
  | neutral red normal =>
      obtain ⟨red⟩ := red
      refine ⟨⟨_, ⟨red⟩, normal, ⟨.refl (typeEndpoints red.equal).right⟩⟩, ?_⟩
      rintro t ⟨nf, ⟨path⟩, normal⟩
      exact ⟨nf, nf, ⟨path⟩, ⟨path⟩, normal, normal, ⟨.refl path.endpoints.right⟩⟩
  | pi red domain codomain family _ _ domainIH codomainIH =>
      obtain ⟨domain⟩ := domain
      obtain ⟨codomain⟩ := codomain
      refine ⟨⟨_, _, red, ⟨.refl (.pi domain codomain)⟩,
        fun w => (domainIH w).type, fun {m} {Δ} {ρ} w {a} argument => (codomainIH w argument).type⟩, ?_⟩
      intro t member
      have copy := member
      obtain ⟨nf, ⟨path⟩, _normal, applications, _extension⟩ := copy
      exact ⟨member, member, nf, nf, ⟨path⟩, ⟨path⟩, ⟨.refl path.endpoints.right⟩,
        fun {m} {Δ} {ρ} w {a} argument => (codomainIH w argument).term (applications w argument)⟩

theorem LogRel.reflexive {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) : Reflexive A P := by
  induction bound using Nat.strong_induction_on generalizing n Γ A P with
  | h bound ih =>
      refine LR.reflexive ?_ related
      intro k less n Δ B Q relatedQ
      exact ih k less ((below_iff less).mp relatedQ)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
