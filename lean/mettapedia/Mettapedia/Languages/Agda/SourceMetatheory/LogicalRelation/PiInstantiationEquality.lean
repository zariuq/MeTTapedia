import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiApplicationEquality

/-!
Comparison of dependent result types when both the Pi code and its argument
change. This is semantic Pi inversion from the concrete clause, not source
Pi injectivity from an arbitrary derivation of type equality.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LogRel.piInstantiationEquality {bound argumentBound : Nat} {Γ : RawContext n}
    {A A' : Ty n} {B B' : TyAbs n} {P Q : Pack n} {a b : Term n}
    (functionType : LogRel bound Γ (Ty.pi A B) P) (types : P.eqTy (Ty.pi A' B'))
    (argumentType : LogRel argumentBound Γ A Q) (arguments : Q.eqTm a b) :
    LogRel (B.instantiate a).level Γ (B.instantiate a) (annotatedPack Γ (B.instantiate a)) ∧
      (annotatedPack Γ (B.instantiate a)).eqTy (B'.instantiate b) := by
  obtain ⟨family, rfl, ⟨domainFormed⟩, _, domains, codomains⟩ := functionType.piView
  obtain ⟨D, E, ⟨path⟩, _, _, comparisons⟩ := types
  have fixed := path.steps.raw.pi_fixed
  cases fixed
  let world := World.identity domainFormed.context
  have domainRelated : LogRel bound Γ A (family.domain world) := by
    simpa only [Ty.rename_id] using domains world
  have same := argumentType.irrelevantAcross domainRelated
  have argumentComparison : (family.domain world).eqTm a b := same ▸ arguments
  have left := (domainRelated.equalityMembers argumentComparison).1
  have right := (domainRelated.equalityMembers argumentComparison).2
  have leftRelated : LogRel bound Γ (B.instantiate a) (family.codomain world left) := by
    simpa only [TyAbs.rename_id] using codomains world left
  have rightRelated : LogRel bound Γ (B.instantiate b) (family.codomain world right) := by
    simpa only [TyAbs.rename_id] using codomains world right
  have step : (family.codomain world left).eqTy (B.instantiate b) := by
    simpa only [TyAbs.rename_id] using family.extension world left right argumentComparison
  have compared : (family.codomain world right).eqTy (B'.instantiate b) := by
    simpa only [TyAbs.rename_id] using comparisons world right
  refine ⟨leftRelated.annotated, ?_⟩
  rw [leftRelated.annotatedPack_eq]
  exact leftRelated.transitiveTypeEquality rightRelated step compared

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
