import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.Validity
import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropDependentUniverse

/-!
Validity for universes, variables, and universe elimination. The semantic
telescope clauses supply variable membership; source receipts are retained
separately. No derivation of the fundamental theorem is assumed here.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke

theorem SemEqSub.tail {Γ : RawContext n} {A : Ty n} {Δ : RawContext m}
    {σ τ : Substitution (n + 1) m} (valid : SemEqSub (Γ.snoc A) Δ σ τ) :
    SemEqSub Γ Δ (tailSub σ) (tailSub τ) := by
  refine ⟨valid.left.1, valid.right.1, ?_⟩
  intro i
  simpa only [RawContext.lookup_succ, subst_weaken_tail, tailSub, Function.comp_def]
    using valid.equal i.succ

theorem ValidType.weaken {Γ : RawContext n} {A B : Ty n}
    (valid : ValidType Γ B) (added : FormTy Γ A) : ValidType (Γ.snoc A) B.weaken := by
  obtain ⟨source⟩ := valid.source
  refine ⟨⟨source.weaken added⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    simpa only [subst_weaken_tail] using valid.reducible substitution.1
  · intro m Δ σ τ substitution
    simpa only [subst_weaken_tail] using valid.extension substitution.tail

theorem ValidContext.lookup {Γ : RawContext n} (valid : ValidContext Γ) (i : Fin n) :
    ValidType Γ (Γ.lookup i) := by
  induction valid with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A valid domain previous =>
      obtain ⟨formedA⟩ := domain.source
      exact Fin.cases (domain.weaken formedA) (fun j => (previous j).weaken formedA) i

theorem ValidType.universe {Γ : RawContext n} (formed : FormCtx Γ) (k : Nat) :
    ValidType Γ (Ty.universe k) := by
  refine ⟨⟨.universe formed k⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    obtain ⟨target⟩ := substitution.formed
    simpa only [Ty.universe_subst] using
      (universeReducible (k + 1) k (Nat.lt_succ_self k) target).annotated
  · intro m Δ σ τ substitution
    obtain ⟨target⟩ := substitution.left.formed
    simpa only [Ty.universe_subst] using
      (universeReducible (k + 1) k (Nat.lt_succ_self k) target).annotated.reflexive.type

theorem ValidTerm.sort {Γ : RawContext n} (formed : FormCtx Γ) (k : Nat) :
    ValidTerm Γ (.sort k) (Ty.universe (k + 1)) := by
  refine ⟨⟨.sort k formed⟩, .universe formed (k + 1), ?_, ?_⟩
  · intro m Δ σ substitution
    obtain ⟨target⟩ := substitution.formed
    simp only [Ty.universe_subst, Term.subst]
    rw [(universeReducible (k + 2) (k + 1) (Nat.lt_succ_self (k + 1)) target).annotatedPack_eq]
    exact sortMember k target
  · intro m Δ σ τ substitution
    obtain ⟨target⟩ := substitution.left.formed
    simp only [Ty.universe_subst, Term.subst]
    have related := universeReducible (k + 2) (k + 1) (Nat.lt_succ_self (k + 1)) target
    rw [related.annotatedPack_eq]
    exact related.reflexive.term (sortMember k target)

theorem ValidTerm.var {Γ : RawContext n} (context : ValidContext Γ) (i : Fin n) :
    ValidTerm Γ (.var i) (Γ.lookup i) := by
  obtain ⟨formed⟩ := context.formed
  exact ⟨⟨.var i formed⟩, context.lookup i,
    fun substitution => (substitution.lookup i).2, fun substitution => substitution.equal i⟩

theorem ValidType.ofTyping {Γ : RawContext n} {t : Term n} {k : Nat}
    (valid : ValidTerm Γ t (Ty.universe k)) : ValidType Γ (.el k t) := by
  obtain ⟨typed⟩ := valid.source
  refine ⟨⟨.ofTyping typed⟩, ?_, ?_⟩
  · intro m Δ σ substitution
    obtain ⟨target⟩ := substitution.formed
    have member := valid.member substitution
    simp only [Ty.universe_subst] at member
    rw [(universeReducible (k + 1) k (Nat.lt_succ_self k) target).annotatedPack_eq] at member
    exact universeMember_decode (Nat.lt_succ_self k) member
  · intro m Δ σ τ substitution
    obtain ⟨target⟩ := substitution.left.formed
    have equal := valid.extension substitution
    simp only [Ty.universe_subst] at equal
    rw [(universeReducible (k + 1) k (Nat.lt_succ_self k) target).annotatedPack_eq] at equal
    exact universeEquality_decode (Nat.lt_succ_self k) equal

theorem ValidTypeEq.atSort {Γ : RawContext n} {t u : Term n} {k : Nat}
    (valid : ValidTermEq Γ t u (Ty.universe k)) : ValidTypeEq Γ (.el k t) (.el k u) := by
  obtain ⟨source⟩ := valid.source
  refine ⟨⟨.atSort source⟩, .ofTyping valid.left, .ofTyping valid.right, ?_⟩
  intro m Δ σ substitution
  obtain ⟨target⟩ := substitution.formed
  have equal := valid.equal substitution
  simp only [Ty.universe_subst] at equal
  rw [(universeReducible (k + 1) k (Nat.lt_succ_self k) target).annotatedPack_eq] at equal
  exact universeEquality_decode (Nat.lt_succ_self k) equal

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
