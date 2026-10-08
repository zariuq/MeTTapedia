import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Functionality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# Dependent typed substitution congruence

These laws use the actual typing and equality judgments. A formed source
telescope lets functionality compare the two substituted lookup types;
that comparison supplies the retyping required by symmetry and transitivity.
Both orders of composition and extension by a supplied newest component
retain those dependent annotations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

open Normalization

variable {Head : Type} {R : Rules Head}

theorem SubstMor.identity {n : Nat} (Γ : Ctx Head n) : SubstMor R Γ Γ ids := by
  intro index
  simpa only [ids, subst_ids] using (Derivable.var (R := R) (Γ := Γ) index)

theorem SubstMor.compose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {earlier : Sub Head m k} {later : Sub Head n m}
    (first : SubstMor R Δ Θ earlier) (second : SubstMor R Γ Δ later) :
    SubstMor R Γ Θ (subComp earlier later) := by
  intro index
  change Typed R Θ (subst earlier (later index))
    (subst (subComp earlier later) (Ctx.lookup Γ index))
  rw [← subst_subComp]
  exact (second index).substitute first

theorem SubstMor.cons {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (typed : SubstMor R Γ Δ σ)
    (A : Tm Head n) {term : Tm Head m} (component : Typed R Δ term (subst σ A)) :
    SubstMor R (.snoc Γ A) Δ (consSub term σ) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [Ctx.lookup_snoc_zero, consSub_zero, subst_consSub_rename_wk] using component
  · intro prior
    simpa only [Ctx.lookup_snoc_succ, consSub_succ, subst_consSub_rename_wk] using typed prior

theorem SubstEq.reflexive {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (typed : SubstMor R Γ Δ σ) : SubstEq R Γ Δ σ σ :=
  ⟨typed, fun index => .refl (typed index)⟩

theorem SubstEq.annotation {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    (formed : CtxFormed R Γ) {σ τ : Sub Head n m} (same : SubstEq R Γ Δ σ τ)
    (index : Fin n) :
    TypeEq R Δ (subst σ (Ctx.lookup Γ index)) (subst τ (Ctx.lookup Γ index)) := by
  obtain ⟨level, universeWitness, typed⟩ := formed.lookup index
  exact ⟨level, universeWitness, by simpa only [subst] using typed.functional same⟩

theorem SubstEq.symmetric {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    (formed : CtxFormed R Γ) {σ τ : Sub Head n m} (secondTyped : SubstMor R Γ Δ τ)
    (same : SubstEq R Γ Δ σ τ) : SubstEq R Γ Δ τ σ :=
  ⟨secondTyped, fun index => Equal.convType (.symm (same.2 index)) (same.annotation formed index)⟩

theorem SubstEq.transitive {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    (formed : CtxFormed R Γ) {σ τ υ : Sub Head n m}
    (earlier : SubstEq R Γ Δ σ τ) (later : SubstEq R Γ Δ τ υ) : SubstEq R Γ Δ σ υ :=
  ⟨earlier.1, fun index => .trans (earlier.2 index)
    (Equal.convType (later.2 index) (earlier.annotation formed index).symm)⟩

theorem SubstEq.precompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ τ : Sub Head n m} (same : SubstEq R Γ Δ σ τ)
    {earlier : Sub Head m k} (typed : SubstMor R Δ Θ earlier) :
    SubstEq R Γ Θ (subComp earlier σ) (subComp earlier τ) := by
  refine ⟨typed.compose same.1, ?_⟩
  intro index
  change Equal R Θ (subst earlier (σ index)) (subst earlier (τ index))
    (subst (subComp earlier σ) (Ctx.lookup Γ index))
  rw [← subst_subComp]
  exact (same.2 index).substitute typed

theorem SubstEq.postcompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ τ : Sub Head m k} (same : SubstEq R Δ Θ σ τ)
    {later : Sub Head n m} (typed : SubstMor R Γ Δ later) :
    SubstEq R Γ Θ (subComp σ later) (subComp τ later) := by
  refine ⟨same.1.compose typed, ?_⟩
  intro index
  change Equal R Θ (subst σ (later index)) (subst τ (later index))
    (subst (subComp σ later) (Ctx.lookup Γ index))
  rw [← subst_subComp]
  exact (typed index).functional same

theorem SubstEq.compose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    (formed : CtxFormed R Γ)
    {σ σ' : Sub Head m k} {τ τ' : Sub Head n m}
    (earlier : SubstEq R Δ Θ σ σ') (later : SubstEq R Γ Δ τ τ')
    (earlierTyped : SubstMor R Δ Θ σ') :
    SubstEq R Γ Θ (subComp σ τ) (subComp σ' τ') :=
  (earlier.postcompose later.1).transitive formed (later.precompose earlierTyped)

theorem SubstEq.cons {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ τ : Sub Head n m} (same : SubstEq R Γ Δ σ τ) (A : Tm Head n)
    {first second : Tm Head m} (typed : Typed R Δ first (subst σ A))
    (component : Equal R Δ first second (subst σ A)) :
    SubstEq R (.snoc Γ A) Δ (consSub first σ) (consSub second τ) := by
  refine ⟨same.1.cons A typed, ?_⟩
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [Ctx.lookup_snoc_zero, consSub_zero, subst_consSub_rename_wk] using component
  · intro prior
    simpa only [Ctx.lookup_snoc_succ, consSub_succ, subst_consSub_rename_wk] using same.2 prior

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
