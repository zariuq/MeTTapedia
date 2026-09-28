import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TypedExpansion

/-!
The semantic application case uses the actual Pi clauses, pack coherence,
and explicitly typed reduction under an application head. Its output type
is the dependent codomain instantiated by the supplied source argument.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LogRel.application {bound argumentBound : Nat} {Γ : RawContext n}
    {A : Ty n} {B : TyAbs n} {P Q : Pack n} {f a : Term n}
    (functionType : LogRel bound Γ (Ty.pi A B) P) (function : P.redTm f)
    (argumentType : LogRel argumentBound Γ A Q) (argument : Q.redTm a) :
    LogRel (B.instantiate a).level Γ (B.instantiate a) (annotatedPack Γ (B.instantiate a)) ∧
      (annotatedPack Γ (B.instantiate a)).redTm (f.app a) := by
  obtain ⟨family, rfl, ⟨domainFormed⟩, _, domains, codomains⟩ := functionType.piView
  let world := World.identity domainFormed.context
  have domainRelated : LogRel bound Γ A (family.domain world) := by
    simpa only [Ty.rename_id] using domains world
  have sameDomain := argumentType.irrelevantAcross domainRelated
  have argumentInFamily : (family.domain world).redTm a := sameDomain ▸ argument
  have codomainRelated : LogRel bound Γ (B.instantiate a) (family.codomain world argumentInFamily) := by
    simpa only [TyAbs.rename_id] using codomains world argumentInFamily
  obtain ⟨nf, ⟨path⟩, _, applications, _⟩ := function
  have headMember : (family.codomain world argumentInFamily).redTm (nf.app a) := by
    simpa only [Term.rename_id] using applications world argumentInFamily
  obtain ⟨argumentTyped⟩ := argumentType.escape.typing argument
  have applicationMember := codomainRelated.expandTerm
    (typedRedApplication path argumentTyped) headMember
  refine ⟨codomainRelated.annotated, ?_⟩
  rw [codomainRelated.annotatedPack_eq]
  exact applicationMember

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
