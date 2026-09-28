import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropNeutral

/-!
Semantic Pi shape and component extraction. These theorems require actual
logical-relation evidence and semantic type equality. They do not promote
arbitrary source TypeEq to semantic equality; that needs the still separate
fundamental theorem. Fresh-variable reflection is derived in PropNeutral.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LogRel.piView {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {P : Pack n} (related : LogRel bound Γ (Ty.pi A B) P) :
    ∃ family : PiFamily Γ A B, P = piPack Γ A B family ∧
      Nonempty (FormTy Γ A) ∧ Nonempty (FormTy (Γ.snoc A) B.open) ∧
      (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ),
        LogRel bound Δ (A.rename ρ) (family.domain w)) ∧
      (∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (w : World Γ Δ ρ)
        {a : Term m} (argument : (family.domain w).redTm a),
        LogRel bound Δ ((B.rename ρ).instantiate a) (family.codomain w argument)) := by
  cases related with
  | «universe» _ red =>
      obtain ⟨red⟩ := red
      have impossible := red.steps.raw.pi_fixed
      cases impossible
  | neutral red neutral =>
      obtain ⟨red⟩ := red
      obtain ⟨neutral⟩ := neutral
      have impossible := red.steps.raw.pi_fixed
      have atPi : Neutral (.pi A B) := impossible ▸ neutral
      cases atPi
  | pi red domain codomain family domains codomains =>
      obtain ⟨red⟩ := red
      obtain ⟨rfl, rfl⟩ := Term.pi.inj red.steps.raw.pi_fixed
      exact ⟨family, rfl, domain, codomain, domains, codomains⟩

private theorem instantiate_extended (B : TyAbs n) (ρ : Renaming n m) :
    (B.rename (Fin.succ ∘ ρ)).instantiate (.var 0) = (B.rename ρ).open := by
  rw [← TyAbs.rename_comp B ρ Fin.succ, TyAbs.instantiate_weaken_var]

/-- Semantic component comparisons return source equality after every actual
formed world, including the appropriate extension for the opened codomain. -/
theorem LogRel.piComponentsAt {bound : Nat} {Γ : RawContext n} {A A' : Ty n}
    {B B' : TyAbs n} {P : Pack n} (related : LogRel bound Γ (Ty.pi A B) P)
    (equal : P.eqTy (Ty.pi A' B')) {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) :
    Nonempty (TypeEq Δ (A.rename ρ) (A'.rename ρ)) ∧
    Nonempty (TypeEq (Δ.snoc (A.rename ρ)) (B.rename ρ).open (B'.rename ρ).open) := by
  obtain ⟨family, rfl, ⟨formed⟩, _, domains, codomains⟩ := related.piView
  obtain ⟨_, _, ⟨rightRed⟩, _, equalDomains, equalCodomains⟩ := equal
  obtain ⟨rfl, rfl⟩ := Term.pi.inj rightRed.steps.raw.pi_fixed
  have renamedForm := formed.rename ρ world.respects world.targetFormed
  let extended := world.comp (World.weaken renamedForm)
  have newestTyped : Typing (Δ.snoc (A.rename ρ)) (.var 0) (A.rename (Fin.succ ∘ ρ)) := by
    simpa only [RawContext.lookup_zero, Ty.weaken, Ty.rename_comp] using
      (Typing.var 0 (FormCtx.snoc world.targetFormed renamedForm))
  have newest : (family.domain extended).redTm (.var 0) :=
    (domains extended).neutralReflection.term (.var 0) newestTyped
  have codomainEquality := (codomains extended newest).escape.typeEquality
    (equalCodomains extended newest)
  refine ⟨(domains world).escape.typeEquality (equalDomains world), ?_⟩
  obtain ⟨codomainEquality⟩ := codomainEquality
  exact ⟨by simpa only [instantiate_extended] using codomainEquality⟩

/-- Actual Type-valued component derivations, reconstructed without choice. -/
def LogRel.piComponentEvidenceAt {bound : Nat} {Γ : RawContext n} {A A' : Ty n}
    {B B' : TyAbs n} {P : Pack n} (related : LogRel bound Γ (Ty.pi A B) P)
    (equal : P.eqTy (Ty.pi A' B')) {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) :
    TypeEq Δ (A.rename ρ) (A'.rename ρ) ×
      TypeEq (Δ.snoc (A.rename ρ)) (B.rename ρ).open (B'.rename ρ).open :=
  let parts := related.piComponentsAt equal world
  ⟨Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverTypeEquality parts.1, Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverTypeEquality parts.2⟩

theorem LogRel.piNotUniverse {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {P : Pack n} (related : LogRel bound Γ (Ty.pi A B) P) (k : Nat) :
    ¬ P.eqTy (Ty.universe k) := by
  obtain ⟨_, rfl, _⟩ := related.piView
  rintro ⟨_, _, ⟨red⟩, _⟩
  have impossible := red.steps.raw.sort_fixed
  cases impossible

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
