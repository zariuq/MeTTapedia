import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiIntroduction

/-! Concrete renaming actions on the neutral and Kripke Pi clauses. -/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure RenamePack (ρ : Renaming n m) (P : Pack n) (Q : Pack m) : Prop where
  types : ∀ {A}, P.eqTy A → Q.eqTy (A.rename ρ)
  terms : ∀ {t}, P.redTm t → Q.redTm (t.rename ρ)
  equalities : ∀ {t u}, P.eqTm t u → Q.eqTm (t.rename ρ) (u.rename ρ)

def PiFamily.after {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (family : PiFamily Γ A B) {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) :
    PiFamily Δ (A.rename ρ) (B.rename ρ) where
  domain {_k} {_Θ} {_τ} future := family.domain (world.comp future)
  codomain {_k} {_Θ} {_τ} future {_a} argument := family.codomain (world.comp future) argument
  extension := by
    intro k Θ τ future a b left right equal
    simpa only [TyAbs.rename_comp] using family.extension (world.comp future) left right equal

theorem neutralPack_rename {Γ : RawContext n} {A : Ty n}
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) :
    RenamePack ρ (neutralPack Γ A) (neutralPack Δ (A.rename ρ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro B ⟨C, ⟨path⟩, ⟨normal⟩, ⟨equal⟩⟩
    exact ⟨C.rename ρ, ⟨path.rename world⟩,
      ⟨by simpa only [typeTerm_rename] using normal.rename ρ⟩, ⟨world.typeEquality equal⟩⟩
  · rintro t ⟨nf, ⟨path⟩, ⟨normal⟩⟩
    exact ⟨nf.rename ρ, ⟨world.reduction path⟩, ⟨normal.rename ρ⟩⟩
  · rintro t u ⟨nf, ng, ⟨left⟩, ⟨right⟩, ⟨leftNormal⟩, ⟨rightNormal⟩, ⟨equal⟩⟩
    exact ⟨nf.rename ρ, ng.rename ρ, ⟨world.reduction left⟩, ⟨world.reduction right⟩,
      ⟨leftNormal.rename ρ⟩, ⟨rightNormal.rename ρ⟩, ⟨world.termEquality equal⟩⟩

theorem piPack_rename {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) :
    RenamePack ρ (piPack Γ A B family)
      (piPack Δ (A.rename ρ) (B.rename ρ) (family.after world)) := by
  have terms : ∀ {t}, PiRedTm family t → PiRedTm (family.after world) (t.rename ρ) := by
    rintro t ⟨nf, ⟨path⟩, ⟨normal⟩, applications, extension⟩
    refine ⟨nf.rename ρ, ?_, ⟨normal.rename ρ⟩, ?_, ?_⟩
    · exact ⟨by simpa only [Ty.pi_rename] using world.reduction path⟩
    · intro k Θ τ future a argument
      simpa only [PiFamily.after, Term.rename_comp] using applications (world.comp future) argument
    · intro k Θ τ future a b left right equal
      simpa only [PiFamily.after, Term.rename_comp] using extension (world.comp future) left right equal
  refine ⟨?_, terms, ?_⟩
  · rintro C ⟨D, E, ⟨path⟩, ⟨equal⟩, domains, codomains⟩
    refine ⟨D.rename ρ, E.rename ρ, ?_, ?_, ?_, ?_⟩
    · exact ⟨by simpa only [Ty.pi_rename] using path.rename world⟩
    · exact ⟨by simpa only [Ty.pi_rename] using world.typeEquality equal⟩
    · intro k Θ τ future
      simpa only [PiFamily.after, Ty.rename_comp] using domains (world.comp future)
    · intro k Θ τ future a argument
      simpa only [PiFamily.after, TyAbs.rename_comp] using codomains (world.comp future) argument
  · rintro t u ⟨leftMember, rightMember, nf, ng, ⟨left⟩, ⟨right⟩, ⟨equal⟩, applications⟩
    refine ⟨terms leftMember, terms rightMember, nf.rename ρ, ng.rename ρ, ?_, ?_, ?_, ?_⟩
    · exact ⟨by simpa only [Ty.pi_rename] using world.reduction left⟩
    · exact ⟨by simpa only [Ty.pi_rename] using world.reduction right⟩
    · exact ⟨by simpa only [Ty.pi_rename] using world.termEquality equal⟩
    · intro k Θ τ future a argument
      simpa only [PiFamily.after, Term.rename_comp] using applications (world.comp future) argument

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
