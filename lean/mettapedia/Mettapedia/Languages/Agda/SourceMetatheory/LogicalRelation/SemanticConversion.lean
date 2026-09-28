import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ConversionClauses

/-!
Reducible types related by semantic equality have the same predicates.
Both reducibility premises are genuine inputs; they are not inferred from
arbitrary source conversion. Clause transport is derived recursively from
this semantic comparison, without a Pi-injectivity assumption.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

private theorem typeRedUnique {Γ : RawContext n} {A B C : Ty n}
    (first : TypeRed Γ A B) (second : TypeRed Γ A C)
    (left : Whnf B.term) (right : Whnf C.term) : B = C := by
  have terms := first.steps.raw.normal_unique second.steps.raw left right
  have levels := first.level.symm.trans second.level
  cases B
  cases C
  cases levels
  cases terms
  rfl

theorem LogRel.convertPacks {bound otherBound : Nat} {Γ : RawContext n}
    {A A' : Ty n} {P Q : Pack n} (left : LogRel bound Γ A P)
    (right : LogRel otherBound Γ A' Q) (equal : P.eqTy A') : P = Q := by
  induction left with
  | @«universe» n Γ A k less red =>
      obtain ⟨red⟩ := red
      obtain ⟨targetRed⟩ := equal
      cases right with
      | «universe» less' red' =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.sort _) (.sort _)
          cases same
          have formed := red.steps.endpoints.right.context
          have atLeft : LogRel bound Γ (Ty.universe k) (universePack (below bound) Γ k) :=
            .universe less ⟨.refl (.universe formed k)⟩
          have atRight : LogRel otherBound Γ (Ty.universe k) (universePack (below otherBound) Γ k) :=
            .universe less' ⟨.refl (.universe formed k)⟩
          exact atLeft.irrelevantAcross atRight
      | neutral red' normal' =>
          obtain ⟨red'⟩ := red'
          obtain ⟨normal'⟩ := normal'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.sort _) (.neutral normal')
          have impossible : Neutral (.sort _) := same.symm ▸ normal'
          cases impossible
      | pi red' _ _ _ _ _ =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.sort _) (.pi _ _)
          cases same
  | neutral _ _ =>
      obtain ⟨C, ⟨targetRed⟩, ⟨normal⟩, ⟨comparison⟩⟩ := equal
      cases right with
      | «universe» _ red' =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.neutral normal) (.sort _)
          have impossible : Neutral (.sort _) := same ▸ normal
          cases impossible
      | neutral red' normal' =>
          obtain ⟨red'⟩ := red'
          obtain ⟨normal'⟩ := normal'
          have same := typeRedUnique targetRed red' (.neutral normal) (.neutral normal')
          cases same
          exact neutralPack_convert comparison
      | pi red' _ _ _ _ _ =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.neutral normal) (.pi _ _)
          have impossible : Neutral (.pi _ _) := same ▸ normal
          cases impossible
  | pi _ _ _ _ _ _ domainsIH codomainsIH =>
      obtain ⟨D, E, ⟨targetRed⟩, ⟨comparison⟩, domainComparisons, codomainComparisons⟩ := equal
      cases right with
      | «universe» _ red' =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.pi _ _) (.sort _)
          cases same
      | neutral red' normal' =>
          obtain ⟨red'⟩ := red'
          obtain ⟨normal'⟩ := normal'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.pi _ _) (.neutral normal')
          have impossible : Neutral (.pi _ _) := same.symm ▸ normal'
          cases impossible
      | pi red' _ _ _ domains' codomains' =>
          obtain ⟨red'⟩ := red'
          have same := targetRed.steps.raw.normal_unique red'.steps.raw (.pi _ _) (.pi _ _)
          obtain ⟨rfl, rfl⟩ := Term.pi.inj same
          apply piPack_convert comparison
          · intro m Δ ρ world
            exact domainsIH world (domains' world) (domainComparisons world)
          · intro m Δ ρ world a left right
            exact codomainsIH world left (codomains' world right) (codomainComparisons world left)

theorem LogRel.symmetricTypeEquality {bound otherBound : Nat} {Γ : RawContext n}
    {A A' : Ty n} {P Q : Pack n} (left : LogRel bound Γ A P)
    (right : LogRel otherBound Γ A' Q) (equal : P.eqTy A') : Q.eqTy A :=
  left.convertPacks right equal ▸ left.reflexive.type

theorem LogRel.transitiveTypeEquality {bound otherBound : Nat} {Γ : RawContext n}
    {A B C : Ty n} {P Q : Pack n} (left : LogRel bound Γ A P)
    (middle : LogRel otherBound Γ B Q) (first : P.eqTy B) (second : Q.eqTy C) : P.eqTy C :=
  (left.convertPacks middle first).symm ▸ second

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
