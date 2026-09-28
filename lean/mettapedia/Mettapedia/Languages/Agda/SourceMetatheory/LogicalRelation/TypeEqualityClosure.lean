import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticConversion

/-!
Semantic type equality produces a reducible target. For Pi targets the new
family is built from canonical predicates, and its extension law follows
from recursively derived comparisons. No target reducibility, Pi inversion,
or fundamental theorem is assumed.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LogRel.typeEqualityTarget {bound : Nat} {Γ : RawContext n} {A C : Ty n}
    {P : Pack n} (related : LogRel bound Γ A P) (equal : P.eqTy C) :
    ∃ Q, LogRel bound Γ C Q := by
  induction related with
  | «universe» less _ => exact ⟨_, .universe less equal⟩
  | neutral _ _ =>
      obtain ⟨_, red, normal, _⟩ := equal
      exact ⟨_, .neutral red normal⟩
  | @pi n Γ A domain codomain _ _ _ family domains codomains domainsIH codomainsIH =>
      obtain ⟨D, E, ⟨targetRed⟩, ⟨sourceEqual⟩, domainComparisons, codomainComparisons⟩ := equal
      have domainsRelated : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m}
          (world : World Γ Δ ρ),
          LogRel bound Δ (D.rename ρ) (canonicalPack bound Δ (D.rename ρ)) := by
        intro m Δ ρ world
        exact canonicalPack_related (domainsIH world (domainComparisons world))
      have domainsEqual : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m}
          (world : World Γ Δ ρ), family.domain world = canonicalPack bound Δ (D.rename ρ) := by
        intro m Δ ρ world
        exact LogRel.convertPacks (domains world) (domainsRelated world) (domainComparisons world)
      have codomainsRelated : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m}
          (world : World Γ Δ ρ) {a : Term m},
          (canonicalPack bound Δ (D.rename ρ)).redTm a →
          LogRel bound Δ ((E.rename ρ).instantiate a)
            (canonicalPack bound Δ ((E.rename ρ).instantiate a)) := by
        intro m Δ ρ world a argument
        have oldArgument : (family.domain world).redTm a := (domainsEqual world).symm ▸ argument
        exact canonicalPack_related (codomainsIH world oldArgument (codomainComparisons world oldArgument))
      have codomainsEqual : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m}
          (world : World Γ Δ ρ) {a : Term m} (oldArgument : (family.domain world).redTm a)
          (newArgument : (canonicalPack bound Δ (D.rename ρ)).redTm a),
          family.codomain world oldArgument = canonicalPack bound Δ ((E.rename ρ).instantiate a) := by
        intro m Δ ρ world a oldArgument newArgument
        exact LogRel.convertPacks (codomains world oldArgument) (codomainsRelated world newArgument)
          (codomainComparisons world oldArgument)
      let newFamily : PiFamily Γ D E := {
        domain := fun {_m} {Δ} {ρ} _world => canonicalPack bound Δ (D.rename ρ)
        codomain := fun {_m} {Δ} {ρ} _world {a} _argument =>
          canonicalPack bound Δ ((E.rename ρ).instantiate a)
        extension := by
          intro m Δ ρ world a b left right comparison
          have oldLeft : (family.domain world).redTm a := (domainsEqual world).symm ▸ left
          have oldRight : (family.domain world).redTm b := (domainsEqual world).symm ▸ right
          have oldComparison : (family.domain world).eqTm a b := (domainsEqual world).symm ▸ comparison
          have instantiatedEqual := family.extension world oldLeft oldRight oldComparison
          have oldCodomainsEqual := LogRel.convertPacks (codomains world oldLeft)
            (codomains world oldRight) instantiatedEqual
          have oldToNew : (family.codomain world oldLeft).eqTy ((E.rename ρ).instantiate b) :=
            oldCodomainsEqual.symm ▸ codomainComparisons world oldRight
          exact codomainsEqual world oldLeft left ▸ oldToNew }
      have parts := formationPiParts (typeEndpoints sourceEqual).right
      exact ⟨_, LR.pi ⟨targetRed⟩ ⟨parts.1⟩ ⟨parts.2⟩ newFamily domainsRelated codomainsRelated⟩

/-- Semantic conversion itself supplies the target's canonical relation and
preserves all three predicates. -/
theorem LogRel.typeEqualityCanonical {bound : Nat} {Γ : RawContext n} {A C : Ty n}
    {P : Pack n} (related : LogRel bound Γ A P) (equal : P.eqTy C) :
    LogRel C.level Γ C (annotatedPack Γ C) ∧ P = annotatedPack Γ C := by
  obtain ⟨Q, target⟩ := related.typeEqualityTarget equal
  exact ⟨target.annotated, (related.convertPacks target equal).trans target.annotatedPack_eq.symm⟩

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
