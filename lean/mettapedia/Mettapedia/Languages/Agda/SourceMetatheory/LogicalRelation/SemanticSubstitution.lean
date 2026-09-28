import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.SemanticRenaming

/-!
Finite telescope substitutions interpreted by the actual semantic relation.
The canonical predicates use the exact annotation level. Their source
substitution receipts are reconstructed constructively; no category law or
identity of retained receipt histories is asserted.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke

abbrev tailSub (σ : Substitution (n + 1) m) : Substitution n m := σ ∘ Fin.succ

@[simp] theorem subst_weaken_tail (A : Ty n) (σ : Substitution (n + 1) m) :
    A.weaken.subst σ = A.subst (tailSub σ) := Ty.subst_rename A Fin.succ σ

def SemSub : {n m : Nat} → RawContext n → RawContext m → Substitution n m → Prop
  | _, _, .nil, Δ, _ => Nonempty (FormCtx Δ)
  | _, _, .snoc Γ A, Δ, σ => SemSub Γ Δ (tailSub σ) ∧
      LogRel (A.subst (tailSub σ)).level Δ (A.subst (tailSub σ))
        (annotatedPack Δ (A.subst (tailSub σ))) ∧
      (annotatedPack Δ (A.subst (tailSub σ))).redTm (σ 0)

theorem SemSub.formed {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (valid : SemSub Γ Δ σ) : Nonempty (FormCtx Δ) := by
  induction Γ with
  | nil => exact valid
  | snoc _ _ ih => exact ih valid.1

theorem SemSub.lookup {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (valid : SemSub Γ Δ σ) (i : Fin n) :
    LogRel ((Γ.lookup i).subst σ).level Δ ((Γ.lookup i).subst σ)
      (annotatedPack Δ ((Γ.lookup i).subst σ)) ∧
      (annotatedPack Δ ((Γ.lookup i).subst σ)).redTm (σ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | snoc Γ A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [RawContext.lookup_zero, subst_weaken_tail] using valid.2
      · simpa only [RawContext.lookup_succ, subst_weaken_tail, tailSub, Function.comp_def] using ih valid.1 j

def SemSub.sourceEvidence {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (valid : SemSub Γ Δ σ) (source : FormCtx Γ) : SubDeriv Γ Δ σ where
  source := source
  target := Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverContext valid.formed
  lookup i := (valid.lookup i).1.typingEvidence (valid.lookup i).2

theorem SemSub.pair {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (valid : SemSub Γ Δ σ) {A : Ty n} {a : Term m}
    (related : LogRel (A.subst σ).level Δ (A.subst σ) (annotatedPack Δ (A.subst σ)))
    (member : (annotatedPack Δ (A.subst σ)).redTm a) :
    SemSub (Γ.snoc A) Δ (Substitution.pair σ a) := ⟨valid, related, member⟩

theorem SemSub.renaming {Γ : RawContext n} {Δ : RawContext m} {Θ : RawContext k}
    {σ : Substitution n m} {ρ : Renaming m k} (valid : SemSub Γ Δ σ)
    (world : World Δ Θ ρ) : SemSub Γ Θ (fun i => (σ i).rename ρ) := by
  induction Γ with
  | nil => exact ⟨world.targetFormed⟩
  | snoc Γ A ih =>
      have renamed := valid.2.1.renameCanonical world
      refine ⟨ih valid.1, ?_, ?_⟩
      · simpa only [Ty.rename_subst, tailSub, Function.comp_def] using renamed.1
      · simpa only [Ty.rename_subst, tailSub, Function.comp_def] using renamed.2.terms valid.2.2

structure SemEqSub (Γ : RawContext n) (Δ : RawContext m) (σ τ : Substitution n m) : Prop where
  left : SemSub Γ Δ σ
  right : SemSub Γ Δ τ
  equal : ∀ i, (annotatedPack Δ ((Γ.lookup i).subst σ)).eqTm (σ i) (τ i)

theorem SemSub.reflexive {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (valid : SemSub Γ Δ σ) : SemEqSub Γ Δ σ σ :=
  ⟨valid, valid, fun i => (valid.lookup i).1.reflexive.term (valid.lookup i).2⟩

def SemEqSub.sourceEvidence {Γ : RawContext n} {Δ : RawContext m} {σ τ : Substitution n m}
    (valid : SemEqSub Γ Δ σ τ) (source : FormCtx Γ) : EqualSubstitution Γ Δ σ τ where
  left := valid.left.sourceEvidence source
  right := valid.right.sourceEvidence source
  equal i := (valid.left.lookup i).1.termEqualityEvidence (valid.equal i)

theorem SemEqSub.renaming {Γ : RawContext n} {Δ : RawContext m} {Θ : RawContext k}
    {σ τ : Substitution n m} {ρ : Renaming m k} (valid : SemEqSub Γ Δ σ τ)
    (world : World Δ Θ ρ) :
    SemEqSub Γ Θ (fun i => (σ i).rename ρ) (fun i => (τ i).rename ρ) := by
  refine ⟨valid.left.renaming world, valid.right.renaming world, ?_⟩
  intro i
  have renamed := (valid.left.lookup i).1.renameCanonical world
  simpa only [Ty.rename_subst] using renamed.2.equalities (valid.equal i)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
