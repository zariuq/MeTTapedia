import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.ValidityLambda

/-!
Source beta and typed eta validity. Beta uses the concrete substituted typed
contraction; eta instantiates the actual opened-codomain premise at every
formed world and semantic argument.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem ValidTermEq.beta {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n} {a : Term n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    (bodyValid : ValidTerm (Γ.snoc A) body.open B.open) (argument : ValidTerm Γ a A) :
    ValidTermEq Γ ((Term.lam body).app a) (body.instantiate a) (B.instantiate a) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  obtain ⟨bodyTyping⟩ := bodyValid.source
  obtain ⟨argumentTyping⟩ := argument.source
  apply ValidTermEq.ofLeft (.beta formedA formedB bodyTyping argumentTyping)
    ((ValidTerm.lam domain codomain bodyValid).app argument)
  intro m Δ σ substitution
  have domainRelated := domain.reducible substitution
  have member := argument.member substitution
  have paired := substitution.pair domainRelated member
  have resultRelated := codomain.reducible paired
  have bodyMember := bodyValid.member paired
  have path := betaAfterSubstitution formedA formedB bodyTyping
    (substitution.sourceEvidence formedA.context) (domainRelated.typingEvidence member)
  rw [ty_open_pair] at resultRelated
  rw [ty_open_pair, term_open_pair] at bodyMember
  have compared := resultRelated.expandTermEquality path
    (.refl (resultRelated.typingEvidence bodyMember)) (resultRelated.reflexive.term bodyMember)
  simpa only [TyAbs.instantiate_subst, Abs.instantiate_subst, Term.app_subst, Term.subst]
    using compared

theorem term_weaken_pair (t : Term n) (σ : Substitution n m) (a : Term m) :
    t.weaken.subst (Substitution.pair σ a) = t.subst σ := by
  rw [Term.weaken, Term.subst_rename]
  rfl

theorem ValidTermEq.eta {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {f g : Term n}
    (domain : ValidType Γ A) (codomain : ValidType (Γ.snoc A) B.open)
    (left : ValidTerm Γ f (Ty.pi A B)) (right : ValidTerm Γ g (Ty.pi A B))
    (pointwise : ValidTermEq (Γ.snoc A) (f.weaken.app (.var 0)) (g.weaken.app (.var 0)) B.open) :
    ValidTermEq Γ f g (Ty.pi A B) := by
  obtain ⟨formedA⟩ := domain.source
  obtain ⟨formedB⟩ := codomain.source
  obtain ⟨leftTyping⟩ := left.source
  obtain ⟨rightTyping⟩ := right.source
  obtain ⟨pointwiseSource⟩ := pointwise.source
  apply ValidTermEq.ofLeft (.eta formedA formedB leftTyping rightTyping pointwiseSource) left
  intro m Δ σ substitution
  have related := domain.piRelated codomain substitution
  have leftMember := left.member substitution
  have rightMember := right.member substitution
  simp only [Ty.pi_subst] at leftMember rightMember ⊢
  rw [related.annotatedPack_eq] at leftMember rightMember ⊢
  let actual := substitution.sourceEvidence formedA.context
  have newA := formedA.substitute actual
  have newB : FormTy (Δ.snoc (A.subst σ)) (B.subst σ).open := by
    simpa only [TyAbs.open_subst] using formedB.substitute (actual.lift formedA newA)
  apply piFunctionExtensionality newA newB (domain.piFamily_domains codomain substitution)
    (domain.piFamily_codomains codomain substitution) leftMember rightMember
  intro k Θ ρ world a argument
  have tail := substitution.renaming world
  have domainRelated := domain.reducible tail
  have member : (annotatedPack Θ (A.subst (fun i => (σ i).rename ρ))).redTm a := by
    simpa only [ValidType.piFamily, Ty.rename_subst] using argument
  have paired := tail.pair domainRelated member
  have equal := pointwise.equal paired
  simp only [ty_open_pair, Term.app_subst, term_weaken_pair, Term.subst,
    Substitution.pair, Fin.cases_zero] at equal
  simpa only [ValidType.piFamily, ← TyAbs.rename_subst, ← Term.rename_subst] using equal

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
