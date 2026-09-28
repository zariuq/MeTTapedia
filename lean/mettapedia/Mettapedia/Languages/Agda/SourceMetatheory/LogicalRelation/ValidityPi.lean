import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityEquality

/-!
Dependent Pi validity constructed from domain and opened-codomain validity.
Its family uses canonical predicates at the actual substituted codes. Equal
substitutions act on the codomain through paired substitutions, retaining the
transport of the argument across the compared domains.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem ty_open_pair (B : TyAbs n) (σ : Substitution n m) (a : Term m) :
    B.open.subst (Substitution.pair σ a) = (B.subst σ).instantiate a := by
  rw [TyAbs.instantiate, TyAbs.open_subst, Ty.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact (Term.subst_single_weaken (σ j) a).symm

theorem term_open_pair (body : Abs n) (σ : Substitution n m) (a : Term m) :
    body.open.subst (Substitution.pair σ a) = (body.subst σ).instantiate a := by
  rw [Abs.instantiate, Abs.open_subst, Term.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact (Term.subst_single_weaken (σ j) a).symm

def ValidType.piFamily {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SemSub Γ Δ σ) :
    PiFamily Δ (A.subst σ) (B.subst σ) where
  domain {_k} {Θ} {ρ} _world := annotatedPack Θ ((A.subst σ).rename ρ)
  codomain {_k} {Θ} {ρ} _world {a} _argument :=
    annotatedPack Θ (((B.subst σ).rename ρ).instantiate a)
  extension := by
    intro k Θ ρ world a b left right comparison
    have tail := substitution.renaming world
    have related := domain.reducible tail
    simp only [Ty.rename_subst] at left right comparison
    have paired := tail.reflexive.pair related related left right comparison
    simpa only [ty_open_pair, ← TyAbs.rename_subst] using codomain.extension paired

theorem ValidType.piFamily_domains {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SemSub Γ Δ σ)
    {Θ : RawContext k} {ρ : Renaming m k} (world : World Δ Θ ρ) :
    LogRel (Ty.pi (A.subst σ) (B.subst σ)).level Θ ((A.subst σ).rename ρ)
      ((domain.piFamily codomain substitution).domain world) := by
  have related := domain.reducible (substitution.renaming world)
  apply LogRel.raise (bound := (A.subst (fun i => (σ i).rename ρ)).level)
  · change (A.subst (fun i => (σ i).rename ρ)).level ≤ max (A.subst σ).level (B.subst σ).level
    simpa only [Ty.level_subst, TyAbs.level_subst] using Nat.le_max_left A.level B.level
  · simpa only [piFamily, Ty.rename_subst] using related

theorem ValidType.piFamily_codomains {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SemSub Γ Δ σ)
    {Θ : RawContext k} {ρ : Renaming m k} (world : World Δ Θ ρ) {a : Term k}
    (argument : ((domain.piFamily codomain substitution).domain world).redTm a) :
    LogRel (Ty.pi (A.subst σ) (B.subst σ)).level Θ (((B.subst σ).rename ρ).instantiate a)
      ((domain.piFamily codomain substitution).codomain world argument) := by
  have tail := substitution.renaming world
  have domainRelated := domain.reducible tail
  have member : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
    simpa only [piFamily, Ty.rename_subst] using argument
  have related := codomain.reducible (tail.pair domainRelated member)
  apply LogRel.raise (bound := (B.open.subst (Substitution.pair (fun i => (σ i).rename ρ) a)).level)
  · change (B.open.subst (Substitution.pair (fun i => (σ i).rename ρ) a)).level ≤
      max (A.subst σ).level (B.subst σ).level
    simpa only [Ty.level_subst, TyAbs.level_open, TyAbs.level_subst]
      using Nat.le_max_right A.level B.level
  · simpa only [piFamily, ty_open_pair, ← TyAbs.rename_subst] using related

theorem ValidType.piRelated {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SemSub Γ Δ σ) :
    LogRel (Ty.pi (A.subst σ) (B.subst σ)).level Δ (Ty.pi (A.subst σ) (B.subst σ))
      (piPack Δ (A.subst σ) (B.subst σ) (domain.piFamily codomain substitution)) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  let actual := substitution.sourceEvidence formedA.context
  have newA := formedA.substitute actual
  have newB := formedB.substitute (actual.lift formedA newA)
  have codomainFormed : FormTy (Δ.snoc (A.subst σ)) (B.subst σ).open := by
    simpa only [TyAbs.open_subst] using newB
  exact .pi ⟨.refl (.pi newA codomainFormed)⟩ ⟨newA⟩ ⟨codomainFormed⟩
    (domain.piFamily codomain substitution) (domain.piFamily_domains codomain substitution)
    (domain.piFamily_codomains codomain substitution)

theorem ValidType.pi {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open) :
    ValidType Γ (Ty.pi A B) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  have formedPi := FormTy.pi formedA formedB
  refine ⟨⟨formedPi⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    simpa only [Ty.pi_subst] using (domain.piRelated codomain substitution).annotated
  · intro m Δ σ τ substitution
    simp only [Ty.pi_subst]
    rw [(domain.piRelated codomain substitution.left).annotatedPack_eq]
    have sourceEqual := formationFunctionality formedPi (substitution.sourceEvidence formedA.context)
    have rightFormation := formedPi.substitute (substitution.right.sourceEvidence formedA.context)
    refine ⟨A.subst τ, B.subst τ,
      ⟨.refl (by simpa only [Ty.pi_subst] using rightFormation)⟩,
      ⟨by simpa only [Ty.pi_subst] using sourceEqual⟩, ?_, ?_⟩
    · intro k Θ ρ world
      simpa only [piFamily, Ty.rename_subst] using domain.extension (substitution.renaming world)
    · intro k Θ ρ world a argument
      have tails := substitution.renaming world
      have leftDomain := domain.reducible tails.left
      have rightDomain := domain.reducible tails.right
      have same := leftDomain.convertPacks rightDomain (domain.extension tails)
      have leftArgument : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
        simpa only [piFamily, Ty.rename_subst] using argument
      have rightArgument : (annotatedPack Θ (A.subst (fun i => (τ i).rename ρ))).redTm a :=
        same ▸ leftArgument
      have paired := tails.pair leftDomain rightDomain leftArgument rightArgument
        (leftDomain.reflexive.term leftArgument)
      simpa only [piFamily, ty_open_pair, ← TyAbs.rename_subst] using codomain.extension paired

theorem ValidTerm.pi {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open) :
    ValidTerm Γ (.pi A B) (Ty.universe (max A.level B.level)) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  have validPi := domain.pi codomain
  refine ⟨⟨.pi formedA formedB⟩, .universe formedA.context _, ?_, ?_⟩
  · intro m Δ σ substitution
    obtain ⟨target⟩ := substitution.formed
    simp only [Ty.universe_subst, Term.subst]
    rw [(universeReducible (max A.level B.level + 1) (max A.level B.level)
      (Nat.lt_succ_self _) target).annotatedPack_eq]
    exact universeMember (Nat.lt_succ_self _) (by
      simpa only [Ty.pi_subst, Ty.pi, Ty.level, Ty.level_subst, TyAbs.level_subst, Ty.subst, Term.subst]
        using validPi.reducible substitution)
  · intro m Δ σ τ substitution
    obtain ⟨target⟩ := substitution.left.formed
    simp only [Ty.universe_subst, Term.subst]
    rw [(universeReducible (max A.level B.level + 1) (max A.level B.level)
      (Nat.lt_succ_self _) target).annotatedPack_eq]
    apply universeEquality (Nat.lt_succ_self _)
    · simpa only [Ty.pi_subst, Ty.pi, Ty.level, Ty.level_subst, TyAbs.level_subst, Ty.subst, Term.subst]
        using validPi.reducible substitution.left
    · simpa only [Ty.pi_subst, Ty.pi, Ty.level, Ty.level_subst, TyAbs.level_subst, Ty.subst, Term.subst]
        using validPi.reducible substitution.right
    · simpa only [Ty.pi_subst, Ty.pi, Ty.level, Ty.level_subst, TyAbs.level_subst, Ty.subst, Term.subst]
        using validPi.extension substitution

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
