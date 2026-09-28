import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiApplication

/-!
Extensional transport of neutral and Pi semantic clauses. Source conversion
is used on retained typed paths and equations; semantic domain/codomain
comparisons are explicit premises for this clause-level transport lemma.
The relation-level theorem derives those comparisons by induction.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure PackMap (P Q : Pack n) : Prop where
  types : ∀ {A}, P.eqTy A → Q.eqTy A
  terms : ∀ {t}, P.redTm t → Q.redTm t
  equalities : ∀ {t u}, P.eqTm t u → Q.eqTm t u

theorem PackMap.antisymm {P Q : Pack n} (forward : PackMap P Q) (reverse : PackMap Q P) :
    P = Q := by
  have types : P.eqTy = Q.eqTy := funext fun _ => propext ⟨forward.types, reverse.types⟩
  have terms : P.redTm = Q.redTm := funext fun _ => propext ⟨forward.terms, reverse.terms⟩
  have equalities : P.eqTm = Q.eqTm := funext fun _ => funext fun _ =>
    propext ⟨forward.equalities, reverse.equalities⟩
  cases P
  cases Q
  cases types
  cases terms
  cases equalities
  rfl

theorem neutralPack_map {Γ : RawContext n} {A B : Ty n} (equal : TypeEq Γ A B) :
    PackMap (neutralPack Γ A) (neutralPack Γ B) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro C ⟨D, red, normal, ⟨comparison⟩⟩
    exact ⟨D, red, normal, ⟨equal.symm.trans comparison⟩⟩
  · rintro t ⟨nf, ⟨path⟩, normal⟩
    exact ⟨nf, ⟨typedRedConvert path equal⟩, normal⟩
  · rintro t u ⟨nf, ng, ⟨left⟩, ⟨right⟩, leftNormal, rightNormal, ⟨comparison⟩⟩
    exact ⟨nf, ng, ⟨typedRedConvert left equal⟩, ⟨typedRedConvert right equal⟩,
      leftNormal, rightNormal, ⟨.conv comparison equal⟩⟩

theorem neutralPack_convert {Γ : RawContext n} {A B : Ty n} (equal : TypeEq Γ A B) :
    neutralPack Γ A = neutralPack Γ B :=
  (neutralPack_map equal).antisymm (neutralPack_map equal.symm)

theorem piPack_map {Γ : RawContext n} {A D : Ty n} {B E : TyAbs n}
    {family : PiFamily Γ A B} {family' : PiFamily Γ D E}
    (equal : TypeEq Γ (Ty.pi A B) (Ty.pi D E))
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      family.domain world = family'.domain world)
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (left : (family.domain world).redTm a) (right : (family'.domain world).redTm a),
      family.codomain world left = family'.codomain world right) :
    PackMap (piPack Γ A B family) (piPack Γ D E family') := by
  have terms : ∀ {t}, PiRedTm family t → PiRedTm family' t := by
    rintro t ⟨nf, ⟨path⟩, normal, applications, extension⟩
    refine ⟨nf, ⟨typedRedConvert path equal⟩, normal, ?_, ?_⟩
    · intro m Δ ρ world a argument
      have oldArgument : (family.domain world).redTm a := (domains world).symm ▸ argument
      exact codomains world oldArgument argument ▸ applications world oldArgument
    · intro m Δ ρ world a b left right comparison
      have oldLeft : (family.domain world).redTm a := (domains world).symm ▸ left
      have oldRight : (family.domain world).redTm b := (domains world).symm ▸ right
      have oldComparison : (family.domain world).eqTm a b := (domains world).symm ▸ comparison
      exact codomains world oldLeft left ▸ extension world oldLeft oldRight oldComparison
  refine ⟨?_, terms, ?_⟩
  · rintro C ⟨F, G, red, ⟨comparison⟩, equalDomains, equalCodomains⟩
    refine ⟨F, G, red, ⟨equal.symm.trans comparison⟩, ?_, ?_⟩
    · intro m Δ ρ world
      exact domains world ▸ equalDomains world
    · intro m Δ ρ world a argument
      have oldArgument : (family.domain world).redTm a := (domains world).symm ▸ argument
      exact codomains world oldArgument argument ▸ equalCodomains world oldArgument
  · rintro t u ⟨leftMember, rightMember, nf, ng, ⟨left⟩, ⟨right⟩, ⟨comparison⟩, applications⟩
    refine ⟨terms leftMember, terms rightMember, nf, ng,
      ⟨typedRedConvert left equal⟩, ⟨typedRedConvert right equal⟩,
      ⟨.conv comparison equal⟩, ?_⟩
    intro m Δ ρ world a argument
    have oldArgument : (family.domain world).redTm a := (domains world).symm ▸ argument
    exact codomains world oldArgument argument ▸ applications world oldArgument

theorem piPack_convert {Γ : RawContext n} {A D : Ty n} {B E : TyAbs n}
    {family : PiFamily Γ A B} {family' : PiFamily Γ D E}
    (equal : TypeEq Γ (Ty.pi A B) (Ty.pi D E))
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      family.domain world = family'.domain world)
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (left : (family.domain world).redTm a) (right : (family'.domain world).redTm a),
      family.codomain world left = family'.codomain world right) :
    piPack Γ A B family = piPack Γ D E family' :=
  (piPack_map equal domains codomains).antisymm
    (piPack_map equal.symm (fun world => (domains world).symm)
      (fun {_m} {_Δ} {_ρ} world {_a} left right => (codomains world right left).symm))

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
