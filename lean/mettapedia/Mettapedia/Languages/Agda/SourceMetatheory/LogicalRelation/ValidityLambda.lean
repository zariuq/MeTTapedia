import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityApplication
import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiIntroduction

/-!
Lambda validity, including comparison after two equal substitutions. The
right beta path is transported by the actual dependent codomain equation;
its result type is never identified by raw syntactic matching.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

def betaAfterSubstitution {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (bodyTyping : Typing (Γ.snoc A) body.open B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SubDeriv Γ Δ σ)
    {a : Term m} (argument : Typing Δ a (A.subst σ)) :
    TypedRed Δ ((Term.lam (body.subst σ)).app a) ((body.subst σ).instantiate a)
      ((B.subst σ).instantiate a) := by
  have newDomain := domain.substitute substitution
  let lifted := substitution.lift domain newDomain
  have newCodomain := codomain.substitute lifted
  have newBody := bodyTyping.substitute lifted
  have step := TypedStep.beta (body := body.subst σ) (B := B.subst σ) newDomain
    (by simpa only [TyAbs.open_subst] using newCodomain)
    (by simpa only [Abs.open_subst, TyAbs.open_subst] using newBody) argument
  exact .step step (.refl step.endpoints.right)

theorem ValidTerm.lambdaMember {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    (validBody : ValidTerm (Γ.snoc A) body.open B.open)
    {Δ : RawContext m} {σ : Substitution n m} (substitution : SemSub Γ Δ σ) :
    (annotatedPack Δ ((Ty.pi A B).subst σ)).redTm (.lam (body.subst σ)) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  obtain ⟨bodyTyping⟩ := validBody.source
  let actual := substitution.sourceEvidence formedA.context
  have newA := formedA.substitute actual
  let lifted := actual.lift formedA newA
  have newB : FormTy (Δ.snoc (A.subst σ)) (B.subst σ).open := by
    simpa only [TyAbs.open_subst] using formedB.substitute lifted
  have newBody : Typing (Δ.snoc (A.subst σ)) (body.subst σ).open (B.subst σ).open := by
    simpa only [Abs.open_subst, TyAbs.open_subst] using bodyTyping.substitute lifted
  simp only [Ty.pi_subst]
  rw [(domain.piRelated codomain substitution).annotatedPack_eq]
  apply piLambda newA newB newBody (domain.piFamily_domains codomain substitution)
    (domain.piFamily_codomains codomain substitution)
  · intro k Θ ρ world a argument
    have tail := substitution.renaming world
    have domainRelated := domain.reducible tail
    have member : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
      simpa only [ValidType.piFamily, Ty.rename_subst] using argument
    simpa only [ValidType.piFamily, ty_open_pair, term_open_pair, ← TyAbs.rename_subst,
      ← Abs.rename_subst] using validBody.member (tail.pair domainRelated member)
  · intro k Θ ρ world a b left right comparison
    have tail := substitution.renaming world
    have domainRelated := domain.reducible tail
    simp only [ValidType.piFamily, Ty.rename_subst] at left right comparison
    have paired := tail.reflexive.pair domainRelated domainRelated left right comparison
    simpa only [ValidType.piFamily, ty_open_pair, term_open_pair, ← TyAbs.rename_subst,
      ← Abs.rename_subst] using validBody.extension paired

theorem ValidTerm.lam {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    (validBody : ValidTerm (Γ.snoc A) body.open B.open) : ValidTerm Γ (.lam body) (Ty.pi A B) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  obtain ⟨bodyTyping⟩ := validBody.source
  have validPi := domain.pi codomain
  refine ⟨⟨.lam formedA formedB bodyTyping⟩, validPi, ?_, ?_⟩
  · intro m Δ σ substitution
    exact lambdaMember domain codomain validBody substitution
  · intro m Δ σ τ substitution
    have related := domain.piRelated codomain substitution.left
    have same := (validPi.reducible substitution.left).convertPacks
      (validPi.reducible substitution.right) (validPi.extension substitution)
    have left := lambdaMember domain codomain validBody substitution.left
    have right : (annotatedPack Δ ((Ty.pi A B).subst σ)).redTm (.lam (body.subst τ)) :=
      same.symm ▸ lambdaMember domain codomain validBody substitution.right
    simp only [Ty.pi_subst, Term.subst]
    simp only [Ty.pi_subst] at left right
    rw [related.annotatedPack_eq] at left right ⊢
    let actual := substitution.left.sourceEvidence formedA.context
    have newA := formedA.substitute actual
    have newB : FormTy (Δ.snoc (A.subst σ)) (B.subst σ).open := by
      simpa only [TyAbs.open_subst] using formedB.substitute (actual.lift formedA newA)
    apply piFunctionExtensionality newA newB (domain.piFamily_domains codomain substitution.left)
      (domain.piFamily_codomains codomain substitution.left) left right
    intro k Θ ρ world a argument
    have tails := substitution.renaming world
    have leftDomain := domain.reducible tails.left
    have rightDomain := domain.reducible tails.right
    have domainSame := leftDomain.convertPacks rightDomain (domain.extension tails)
    have leftArgument : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
      simpa only [ValidType.piFamily, Ty.rename_subst] using argument
    have rightArgument : (annotatedPack Θ (A.subst (fun i => (τ i).rename ρ))).redTm a :=
      domainSame ▸ leftArgument
    have paired := tails.pair leftDomain rightDomain leftArgument rightArgument
      (leftDomain.reflexive.term leftArgument)
    have resultRelated := codomain.reducible paired.left
    obtain ⟨resultEqual⟩ := resultRelated.escape.typeEquality (codomain.extension paired)
    have leftPath := betaAfterSubstitution formedA formedB bodyTyping
      (tails.left.sourceEvidence formedA.context) (leftDomain.typingEvidence leftArgument)
    have rightPath := betaAfterSubstitution formedA formedB bodyTyping
      (tails.right.sourceEvidence formedA.context) (rightDomain.typingEvidence rightArgument)
    rw [ty_open_pair, ty_open_pair] at resultEqual
    have compared := resultRelated.expandTermEquality
      (by simpa only [ty_open_pair] using leftPath)
      (by simpa only [ty_open_pair] using typedRedConvert rightPath resultEqual.symm)
      (by simpa only [term_open_pair] using validBody.extension paired)
    simpa only [ValidType.piFamily, ty_open_pair, ← TyAbs.rename_subst, ← Abs.rename_subst,
      Term.rename] using compared

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
