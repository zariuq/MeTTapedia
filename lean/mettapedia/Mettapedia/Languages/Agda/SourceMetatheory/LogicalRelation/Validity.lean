import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticSubstitution

/-!
Substitution validity for the frozen source calculus. Validity contains source
well-formedness/typing and the stronger semantic statement under every
semantic substitution, including its action on equal substitutions. These
are definitions of the induction motives, not postulated fundamental laws.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke

structure ValidType (Γ : RawContext n) (A : Ty n) : Prop where
  source : Nonempty (FormTy Γ A)
  reducible : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
    LogRel (A.subst σ).level Δ (A.subst σ) (annotatedPack Δ (A.subst σ))
  extension : ∀ {m : Nat} {Δ : RawContext m} {σ τ : Substitution n m}, SemEqSub Γ Δ σ τ →
    (annotatedPack Δ (A.subst σ)).eqTy (A.subst τ)

structure ValidTerm (Γ : RawContext n) (t : Term n) (A : Ty n) : Prop where
  source : Nonempty (Typing Γ t A)
  type : ValidType Γ A
  member : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
    (annotatedPack Δ (A.subst σ)).redTm (t.subst σ)
  extension : ∀ {m : Nat} {Δ : RawContext m} {σ τ : Substitution n m}, SemEqSub Γ Δ σ τ →
    (annotatedPack Δ (A.subst σ)).eqTm (t.subst σ) (t.subst τ)

structure ValidTypeEq (Γ : RawContext n) (A B : Ty n) : Prop where
  source : Nonempty (TypeEq Γ A B)
  left : ValidType Γ A
  right : ValidType Γ B
  equal : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
    (annotatedPack Δ (A.subst σ)).eqTy (B.subst σ)

structure ValidTermEq (Γ : RawContext n) (t u : Term n) (A : Ty n) : Prop where
  source : Nonempty (TermEq Γ t u A)
  left : ValidTerm Γ t A
  right : ValidTerm Γ u A
  equal : ∀ {m : Nat} {Δ : RawContext m} {σ : Substitution n m}, SemSub Γ Δ σ →
    (annotatedPack Δ (A.subst σ)).eqTm (t.subst σ) (u.subst σ)

inductive ValidContext : {n : Nat} → RawContext n → Prop
  | nil : ValidContext .nil
  | snoc {Γ : RawContext n} {A : Ty n} : ValidContext Γ → ValidType Γ A → ValidContext (Γ.snoc A)

theorem ValidContext.formed {Γ : RawContext n} (valid : ValidContext Γ) : Nonempty (FormCtx Γ) := by
  induction valid with
  | nil => exact ⟨.nil⟩
  | snoc _ domain previous =>
      obtain ⟨formed⟩ := previous
      obtain ⟨domain⟩ := domain.source
      exact ⟨.snoc formed domain⟩

theorem SemEqSub.pair {Γ : RawContext n} {Δ : RawContext m} {σ τ : Substitution n m}
    (valid : SemEqSub Γ Δ σ τ) {A : Ty n} {a b : Term m}
    (leftType : LogRel (A.subst σ).level Δ (A.subst σ) (annotatedPack Δ (A.subst σ)))
    (rightType : LogRel (A.subst τ).level Δ (A.subst τ) (annotatedPack Δ (A.subst τ)))
    (left : (annotatedPack Δ (A.subst σ)).redTm a)
    (right : (annotatedPack Δ (A.subst τ)).redTm b)
    (equal : (annotatedPack Δ (A.subst σ)).eqTm a b) :
    SemEqSub (Γ.snoc A) Δ (Substitution.pair σ a) (Substitution.pair τ b) := by
  refine ⟨valid.left.pair leftType left, valid.right.pair rightType right, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [RawContext.lookup_zero, subst_weaken_tail, tailSub, Substitution.pair,
      Function.comp_def, Fin.cases_zero, Fin.cases_succ] using equal
  · simpa only [RawContext.lookup_succ, subst_weaken_tail, tailSub, Substitution.pair,
      Function.comp_def, Fin.cases_succ] using valid.equal j

@[simp] theorem subst_renaming_variables (A : Ty n) (ρ : Renaming n m) :
    A.subst (fun i => Term.var (ρ i)) = A.rename ρ := by
  simpa only [Ty.subst_id, Term.rename] using (Ty.rename_subst A Term.var ρ).symm

theorem ValidContext.identity {Γ : RawContext n} (valid : ValidContext Γ) :
    SemSub Γ Γ Term.var := by
  induction valid with
  | nil => exact ⟨.nil⟩
  | @snoc n Γ A valid domain previous =>
      obtain ⟨formedA⟩ := domain.source
      have tail := previous.renaming (World.weaken formedA)
      have domainRelated := domain.reducible tail
      have related : LogRel A.weaken.level (Γ.snoc A) A.weaken (annotatedPack (Γ.snoc A) A.weaken) := by
        simpa only [Term.rename, subst_renaming_variables, Ty.weaken] using domainRelated
      have newest : Typing (Γ.snoc A) (.var 0) A.weaken :=
        .var 0 (.snoc formedA.context formedA)
      have member := related.neutralReflection.term (.var 0) newest
      change SemSub Γ (Γ.snoc A) (tailSub Term.var) ∧
        LogRel (A.subst (tailSub Term.var)).level (Γ.snoc A) (A.subst (tailSub Term.var))
          (annotatedPack (Γ.snoc A) (A.subst (tailSub Term.var))) ∧
        (annotatedPack (Γ.snoc A) (A.subst (tailSub Term.var))).redTm (.var 0)
      refine ⟨tail, ?_⟩
      simpa only [tailSub, Function.comp_def, subst_renaming_variables, Ty.weaken] using
        And.intro related member

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
