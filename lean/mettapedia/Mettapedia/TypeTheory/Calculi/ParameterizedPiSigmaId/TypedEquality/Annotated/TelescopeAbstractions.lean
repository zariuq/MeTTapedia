import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.InductivePackage

/-!
# Abstractions over a telescope: typing and β

A function of several arguments is an abstraction over a telescope (`lamsCtx`), and its type is
the dependent function type over that telescope (`pisCtx`). In the annotated judgment, for a
formed telescope `Θ` in a package with a level model:

* the function type over `Θ` of a type over `Θ` is a type (`pisCtx_formed`);
* the abstraction over `Θ` of a term typed over `Θ` has that function type (`lamsCtx_typed`);
* **β over a telescope** (`lamsCtx_apply`): the abstraction applied to terms typed along `Θ`
  equals the body at those terms, at the body's type at them. It is one β-step per entry of
  the telescope, with the congruence of application and the typing of the intermediate
  abstractions; the statement hides them.

The typing rule of an applied term of a telescope type is `applyAlong_typed`
(`InductivePackage.lean`).

Positive example: over the empty telescope the abstraction is the body, and the statement is
reflexivity (`lamsCtx_apply_nil`). Use: the four β-steps of the step of `append`
(`appendStep_apply`, `ObjectAppendByEquations.lean`, in the executable model of the MeTTa
candidate) are one application of `lamsCtx_apply`. Negative example: the hypothesis that the
arguments are typed along the telescope cannot be dropped, since the conclusion types the
body at them; an untyped argument gives an untyped term, and no equality at a type holds of
it: both sides of a derivable equality over a formed context are typed (`CEqual.typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open UniverseLevel (LevelOrder)
open Impredicative.Domain (lamsCtx pisCtx)

variable {Head L : Type} [LevelOrder L] {R : Rules Head} {Q : ChurchRules R}

/-- The dependent function type from a type to a type over it is a type. -/
theorem CIsType.pi (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {C : CTm Head (n + 1)} (domain : CIsType Q Γ A) (codomain : CIsType Q (Γ.snoc A) C) :
    CIsType Q Γ (.pi A C) := by
  obtain ⟨w, hw, typedA⟩ := domain
  obtain ⟨u, hu, typedC⟩ := codomain
  obtain ⟨c, join⟩ := levels.join_exists hw hu
  exact ⟨c, (levels.join_level join).1, .piForm typedA hw typedC hu join⟩

/-- **The function type over a formed telescope of a type over it is a type.** -/
theorem pisCtx_formed (levels : LevelModel R L) {k : Nat} {Θ : CCtx Head k}
    (formed : CCtxFormed Q Θ) :
    ∀ {C : CTm Head k}, CIsType Q Θ C → CIsType Q .nil (pisCtx Θ C) := by
  induction formed with
  | nil => exact fun typeC => typeC
  | snoc _ typeA ih => exact fun typeC => ih (CIsType.pi levels typeA typeC)

/-- **The abstraction over a formed telescope of a typed term has the function type over the
telescope.** -/
theorem lamsCtx_typed (levels : LevelModel R L) {k : Nat} {Θ : CCtx Head k}
    (formed : CCtxFormed Q Θ) :
    ∀ {body C : CTm Head k}, CIsType Q Θ C → CTyped Q Θ body C →
      CTyped Q .nil (lamsCtx Θ body) (pisCtx Θ C) := by
  induction formed with
  | nil => exact fun _ typed => typed
  | snoc _ typeA ih =>
    intro body C typeC typed
    obtain ⟨c, hc, piTyped⟩ := CIsType.pi levels typeA typeC
    obtain ⟨w, hw, typedA⟩ := typeA
    exact ih ⟨c, hc, piTyped⟩ (.lamIntro typedA hw piTyped hc typed)

/-- **β over a telescope**: the abstraction over a formed telescope, applied to terms typed
along the telescope, equals the body at those terms, at the body's type at them. -/
theorem lamsCtx_apply (levels : LevelModel R L) {k : Nat} {Θ : CCtx Head k}
    (formed : CCtxFormed Q Θ) :
    ∀ {body C : CTm Head k}, CIsType Q Θ C → CTyped Q Θ body C →
      ∀ {n : Nat} {Γ : CCtx Head n} (σ : CSub Head k n), CSubstMor Q Θ Γ σ →
        CEqual Q Γ (applyAlong σ (lamsCtx Θ body).liftClosed) (body.subst σ) (C.subst σ) := by
  induction formed with
  | nil =>
    intro body C _ typed n Γ σ _
    show CEqual Q Γ body.liftClosed (body.subst σ) (C.subst σ)
    rw [CTm.subst_closed, CTm.subst_closed]
    exact .refl (CTyped.rename (ρ := Fin.elim0) typed fun i => i.elim0)
  | @snoc m Δ A _ typeA ih =>
    intro body C typeC typed n Γ σ mor
    obtain ⟨c, hc, piTyped⟩ := CIsType.pi levels typeA typeC
    obtain ⟨w, hw, typedA⟩ := typeA
    have tailMor : CSubstMor Q Δ Γ fun i => σ i.succ := fun i => by
      have at_ := mor i.succ
      change CTyped Q Γ (σ i.succ) (((Δ.lookup i).rename wk).subst σ) at at_
      rwa [CTm.subst_rename] at at_
    have argument : CTyped Q Γ (σ 0) (A.subst fun i => σ i.succ) := by
      have at_ := mor 0
      change CTyped Q Γ (σ 0) ((A.rename wk).subst σ) at at_
      rwa [CTm.subst_rename] at at_
    have function := ih ⟨c, hc, piTyped⟩ (.lamIntro typedA hw piTyped hc typed)
      (fun i => σ i.succ) tailMor
    have applied : CEqual Q Γ
        (.app (applyAlong (fun i => σ i.succ) (lamsCtx Δ (.lam A body)).liftClosed) (σ 0))
        (.app (.lam (A.subst fun i => σ i.succ) (body.subst (CTm.liftSub fun i => σ i.succ)))
          (σ 0))
        (CTm.inst0 (σ 0) (C.subst (CTm.liftSub fun i => σ i.succ))) :=
      .appCong (B := C.subst (CTm.liftSub fun i => σ i.succ)) function (.refl argument)
    have beta : CEqual Q Γ
        (.app (.lam (A.subst fun i => σ i.succ) (body.subst (CTm.liftSub fun i => σ i.succ)))
          (σ 0))
        (CTm.inst0 (σ 0) (body.subst (CTm.liftSub fun i => σ i.succ)))
        (CTm.inst0 (σ 0) (C.subst (CTm.liftSub fun i => σ i.succ))) :=
      .betaPi (CTyped.substitute piTyped tailMor) hc
        (CTyped.substitute typed (CSubstMor.lift tailMor A)) argument
    have bodyAt : body.subst σ =
        CTm.inst0 (σ 0) (body.subst (CTm.liftSub fun i => σ i.succ)) := by
      rw [CTm.inst0_subst_liftSub]
      exact congrArg (fun τ => body.subst τ) (CTm.eq_consSub_tail σ)
    have typeAt : C.subst σ = CTm.inst0 (σ 0) (C.subst (CTm.liftSub fun i => σ i.succ)) := by
      rw [CTm.inst0_subst_liftSub]
      exact congrArg (fun τ => C.subst τ) (CTm.eq_consSub_tail σ)
    show CEqual Q Γ
      (.app (applyAlong (fun i => σ i.succ) (lamsCtx Δ (.lam A body)).liftClosed) (σ 0))
      (body.subst σ) (C.subst σ)
    rw [bodyAt, typeAt]
    exact .trans applied beta

/-- Positive example: over the empty telescope the abstraction is the body, and β is
reflexivity. -/
theorem lamsCtx_apply_nil (levels : LevelModel R L) {body C : CTm Head 0}
    (typeC : CIsType Q .nil C) (typed : CTyped Q .nil body C) {n : Nat} {Γ : CCtx Head n} :
    CEqual Q Γ body.liftClosed body.liftClosed C.liftClosed := by
  have applied := lamsCtx_apply levels .nil typeC typed (Γ := Γ) (fun i => i.elim0)
    (fun i => i.elim0)
  rwa [CTm.subst_closed, CTm.subst_closed] at applied

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
