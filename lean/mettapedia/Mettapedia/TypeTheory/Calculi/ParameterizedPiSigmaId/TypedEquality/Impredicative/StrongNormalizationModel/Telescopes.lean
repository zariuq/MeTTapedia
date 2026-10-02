import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes

/-!
# Closed constants from their full applications

A declared constant `f : Π Θ. C` is a valid term of its declared type when its
full application to the variables of `Θ` is a valid term of `C` in `Θ`. A term
is valid at a dependent function type when its application to a fresh variable
is valid at the codomain, one binder at a time:

* its values are related because their applications to related arguments are;
* its realizer instance is a realizer because, after any renaming, its
  application to a realizer of a valid argument realizes the application of the
  value; it is strongly normalizing because a variable realizes the daimon.

A term that computes on the value side to a valid term, and whose realizer
instances lie in every candidate containing the valid term's instances, is
valid.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (WhRed tailSub subst_rename_wk inst0_rename_subst_liftSub)
open UniverseLevel (LevelOrder)
open Consistency (World Morph rename_applyClosed applyClosed_snoc_ids)
open StrongNormalization
open TelescopeAbstraction (closeType applyClosed liftClosed_zero)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-- A valid closed type with valid parts, written as a product over a
telescope, has a valid telescope and a valid codomain with valid parts. -/
theorem ValidTyS.close_parts : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n},
    ValidTyS M .nil (closeType Θ C) → StructuredS M .nil (closeType Θ C) →
      ValidCtxSS M Θ ∧ ValidTyS M Θ C ∧ StructuredS M Θ C
  | _, .nil, _, valid, parts => ⟨trivial, valid, parts⟩
  | _, .snoc Θ A, C, valid, parts => by
      obtain ⟨ctx, _, partsPi⟩ := ValidTyS.close_parts Θ (C := .pi A C) valid parts
      obtain ⟨⟨validA, partsA⟩, validC, partsC⟩ := partsPi
      exact ⟨⟨ctx, validA, partsA⟩, validC, partsC⟩

section Laws

variable (laws : M.Laws)
include laws

/-- A term is a valid term of a dependent function type when its application
to a fresh variable is a valid term of the codomain. -/
theorem ValidTmS.of_app_var {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    {B : Tm Head (n + 1)} (ctx : ValidCtxS M Γ) (validPi : ValidTyS M Γ (.pi A B))
    (validApp : ValidTmS M (.snoc Γ A) (.app (Presentation.rename wk t) (.var 0)) B) :
    ValidTmS M Γ t (.pi A B) := by
  have spine := RootShape.spineHeaded M.realizers.shape
  -- The domain and codomain packs of a Π pack, as denotations of instances.
  have domDen : ∀ {m : Nat} {ξ : World M.reading m} {σ : Sub Head n m} {l : L}
      {Q : ValueSide.PiPack M.value ξ}, Q.Interprets (InterpAt M.value l) (Presentation.subst σ A)
        (Presentation.subst (liftSub σ) B) →
      ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (w : Morph ξ ξ' ρ),
        DenS M.value ξ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A)
          (Q.dom w) := by
    intro m ξ σ l Q interprets k ξ' ρ w
    have interpA := interprets.dom w
    rw [rename_subst] at interpA
    exact ⟨l, interpA⟩
  have codDen : ∀ {m : Nat} {ξ : World M.reading m} {σ : Sub Head n m} {l : L}
      {Q : ValueSide.PiPack M.value ξ}, Q.Interprets (InterpAt M.value l) (Presentation.subst σ A)
        (Presentation.subst (liftSub σ) B) →
      ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (w : Morph ξ ξ' ρ) {a : Tm Head k}
        (ha : (Q.dom w).Val a),
        DenS M.value ξ'
          (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) B)
          (Q.cod w ha) := by
    intro m ξ σ l Q interprets k ξ' ρ w a ha
    have interpB := interprets.cod w ha
    rw [inst0_rename_subst_liftSub] at interpB
    exact ⟨l, interpB⟩
  have app_subst : ∀ {m : Nat} (a : Tm Head m) (σ : Sub Head n m),
      Presentation.subst (consSub a σ) (.app (Presentation.rename wk t) (.var 0)) =
        .app (Presentation.subst σ t) a := by
    intro m a σ
    simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero]
  refine ⟨validPi, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  -- The realizers of the applications.
  have realApp : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren _ k} (w : Morph ξ ξ' ρ)
      {a : Tm Head k} (ha : (Q.dom w).Val a) {r' : Nat} (ρr : Ren _ r') (u : Tm Head r'),
      ((Q.dom w).real a).mem u →
        ((Q.cod w ha).real (.app (Presentation.rename ρ (Presentation.subst σ t)) a)).mem
          (.app (Presentation.rename ρr (Presentation.subst ς t)) u) := by
    intro k ξ' ρ w a ha r' ρr u hu
    have e' := EqSubstS.cons (((e.refl_left laws ctx).rename laws w).renameReal ρr)
      (domDen interprets w) ha hu
    have h := (validApp.2 e' (codDen interprets w ha)).2
    rw [app_subst, app_subst] at h
    rw [rename_subst, rename_subst]
    exact h
  refine ⟨fun {_ ξ' ρ} w {a b} ha hab => ?_, (PiPack.mem_real Q).mpr ⟨?_, ?_⟩⟩
  · have e' := EqSubstS.cons ((e.rename laws w).renameReal wk) (domDen interprets w) hab
      ((Q.dom w).real a |>.var_mem spine (0 : Fin (_ + 1)))
    have h := (validApp.2 e' (codDen interprets w ha)).1
    rw [app_subst, app_subst] at h
    rw [rename_subst, rename_subst]
    exact h
  · have star := DenS.star_val laws.value (domDen interprets (Morph.id ξ))
    have h := realApp (Morph.id ξ) star wk (.var 0)
      (((Q.dom _).real _).var_mem spine (0 : Fin (_ + 1)))
    exact SN.of_rename wk (SN.app_left (KCand.sn _ h))
  · intro k ξ' ρ w a ha r' ρr u hu
    exact realApp w ha ρr u hu

/-- A constant, or any closed term, is a valid term of its closed type when its
full application to the variables of the telescope is valid. -/
theorem ValidTmS.close : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n} {f : Tm Head 0},
    ValidTyS M .nil (closeType Θ C) → StructuredS M .nil (closeType Θ C) →
      ValidTmS M Θ (applyClosed Θ ids (liftClosed f)) C → ValidTmS M .nil f (closeType Θ C)
  | _, .nil, _, f, _, _, valid => by
      rw [show applyClosed (.nil : Ctx Head 0) ids (liftClosed f) = liftClosed f from rfl,
        liftClosed_zero] at valid
      exact valid
  | _, .snoc Θ A, C, f, validType, partsType, valid => by
      obtain ⟨ctx, validPi, _⟩ :=
        ValidTyS.close_parts Θ (C := .pi A C) validType partsType
      refine ValidTmS.close Θ (C := .pi A C) validType partsType
        (ValidTmS.of_app_var laws ctx.valid validPi ?_)
      rw [← applyClosed_snoc_ids]
      exact valid

end Laws

/-- Related valuations give realizers that are strongly normalizing. -/
theorem EqSubstS.real_sn : ∀ {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς →
      ∀ i, SN M.realizers.rules (ς i)
  | _, _, _, _, _, _, _, _, e, i => by
      obtain ⟨_, _, _, hu⟩ := e.lookup i
      exact KCand.sn _ hu

/-- A term is valid when it computes on the value side to a valid term under
every substitution, and its realizer instances, at strongly normalizing
realizers, lie in every candidate containing the valid term's instances. -/
theorem ValidTmS.of_red (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (red : ∀ {m : Nat} (σ : Sub Head n m),
      WhRed M.rules M.roles (Presentation.subst σ t) (Presentation.subst σ u))
    (realRed : ∀ {r : Nat} (ς : Sub Head n r), (∀ i, SN M.realizers.rules (ς i)) →
      ∀ X : M.Cand, X.mem (Presentation.subst ς u) → X.mem (Presentation.subst ς t))
    (valid : ValidTmS M Γ u A) : ValidTmS M Γ t A := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨h, hreal⟩ := rel e den
  have expansive := den.expansive laws.value
  refine ⟨expansive.left (red σ) (expansive.right (red σ') h), ?_⟩
  have same : P.real (Presentation.subst σ t) = P.real (Presentation.subst σ u) :=
    den.real_eq_of_rel laws.value (expansive.left (red σ) (den.refl_left laws.value h))
  rw [same]
  exact realRed ς e.real_sn _ hreal

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
