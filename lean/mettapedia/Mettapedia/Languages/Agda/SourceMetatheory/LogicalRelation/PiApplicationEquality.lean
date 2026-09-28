import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TermEqualityClosure

/-!
Dependent application congruence in the semantic relation. Changing the
argument changes the intermediate source codomain; the right reduction is
transported by the actual source equality escaped from the Pi extension law.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem piMember_extension {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B}
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      LogRel bound Δ (A.rename ρ) (family.domain world))
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      LogRel bound Δ ((B.rename ρ).instantiate a) (family.codomain world argument))
    {f : Term n} (member : PiRedTm family f)
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) {a b : Term m}
    (left : (family.domain world).redTm a) (right : (family.domain world).redTm b)
    (equal : (family.domain world).eqTm a b) :
    (family.codomain world left).eqTm ((f.rename ρ).app a) ((f.rename ρ).app b) := by
  obtain ⟨nf, ⟨path⟩, _, _, extension⟩ := member
  obtain ⟨leftTyped⟩ := (domains world).escape.typing left
  obtain ⟨rightTyped⟩ := (domains world).escape.typing right
  have renamed : TypedRed Δ (f.rename ρ) (nf.rename ρ) (Ty.pi (A.rename ρ) (B.rename ρ)) := by
    simpa only [Ty.pi_rename] using world.reduction path
  obtain ⟨resultEqual⟩ := (codomains world left).escape.typeEquality
    (family.extension world left right equal)
  exact (codomains world left).expandTermEquality
    (typedRedApplication renamed leftTyped)
    (typedRedConvert (typedRedApplication renamed rightTyped) resultEqual.symm)
    (extension world left right equal)

theorem LogRel.applicationCongruence {bound argumentBound : Nat} {Γ : RawContext n}
    {A : Ty n} {B : TyAbs n} {P Q : Pack n} {f g a b : Term n}
    (functionType : LogRel bound Γ (Ty.pi A B) P) (functions : P.eqTm f g)
    (argumentType : LogRel argumentBound Γ A Q) (arguments : Q.eqTm a b) :
    LogRel (B.instantiate a).level Γ (B.instantiate a) (annotatedPack Γ (B.instantiate a)) ∧
      (annotatedPack Γ (B.instantiate a)).eqTm (f.app a) (g.app b) := by
  obtain ⟨family, rfl, ⟨domainFormed⟩, _, domains, codomains⟩ := functionType.piView
  let world := World.identity domainFormed.context
  have domainRelated : LogRel bound Γ A (family.domain world) := by
    simpa only [Ty.rename_id] using domains world
  have sameDomain := argumentType.irrelevantAcross domainRelated
  have equalArguments : (family.domain world).eqTm a b := sameDomain ▸ arguments
  have leftArgument := (domainRelated.equalityMembers equalArguments).1
  have rightArgument := (domainRelated.equalityMembers equalArguments).2
  have codomainRelated : LogRel bound Γ (B.instantiate a) (family.codomain world leftArgument) := by
    simpa only [TyAbs.rename_id] using codomains world leftArgument
  have equalFunctions : (family.codomain world leftArgument).eqTm (f.app a) (g.app a) := by
    simpa only [Term.rename_id] using
      piEquality_pointwise domains codomains functions world leftArgument
  have equalApplications : (family.codomain world leftArgument).eqTm (g.app a) (g.app b) := by
    simpa only [Term.rename_id] using
      piMember_extension domains codomains functions.2.1 world leftArgument rightArgument equalArguments
  refine ⟨codomainRelated.annotated, ?_⟩
  rw [codomainRelated.annotatedPack_eq]
  exact codomainRelated.transitiveTermEquality equalFunctions equalApplications

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
