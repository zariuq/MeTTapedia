import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants

/-!
# Closed constants from their full applications in the conversion model

A declared constant `f : Π Θ. C` is a valid term of its declared type when its
full application to the variables of `Θ` is a valid term of `C` in `Θ`, the
constant is typed at its declared type on the realizer side, and its partial
applications are weak-head normal functions there (`ValidTmN.close`). A term
is valid at a dependent function type when its application to a fresh variable
is valid at the codomain, one binder at a time (`ValidTmN.of_app_var`):

* its values are related because their applications to related arguments are;
* its realizer instances are related by Girard's clause: they are typed weak-head
  normal functions, and after every renaming their applications to realizers of
  a valid argument are related by the realizers of the application of the value,
  which the valuation extended by the argument gives.

A term that computes on the value side to a valid term, and whose realizer
instances compute to those of the valid term by a root step of the realizer
side, is valid (`ValidTmN.of_red`). So a constant defined by one equation, whose
declared type and right-hand side are typed in a package sound for the model,
is valid (`ValidTmN.definition`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph applyClosed_snoc_ids)
open TelescopeAbstraction (closeType applyClosed liftClosed_zero applyClosed_subst)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

/-- A valid closed type with valid parts, written as a product over a
telescope, has a valid telescope and a valid codomain with valid parts. -/
theorem ValidTyN.close_parts : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n},
    ValidTyN M .nil (closeType Θ C) → StructuredN M .nil (closeType Θ C) →
      ValidCtxNN M Θ ∧ ValidTyN M Θ C ∧ StructuredN M Θ C
  | _, .nil, _, valid, parts => ⟨trivial, valid, parts⟩
  | _, .snoc Θ A, C, valid, parts => by
      obtain ⟨ctx, _, partsPi⟩ := ValidTyN.close_parts Θ (C := .pi A C) valid parts
      obtain ⟨⟨validA, partsA⟩, validC, partsC⟩ := partsPi
      exact ⟨⟨ctx, validA, partsA⟩, validC, partsC⟩

/-- The identity is a typed substitution of every context into itself. -/
theorem substMor_ids {R : Rules Head} {n : Nat} (Γ : Ctx Head n) : SubstMor R Γ Γ ids := by
  intro i
  rw [subst_ids]
  exact .var i

section Laws

variable (laws : M.Laws)
include laws

/-- **A term is a valid term of a dependent function type when its application
to a fresh variable is a valid term of the codomain**, the term is typed at the
dependent function type on the realizer side, and its realizer instances are
weak-head normal functions. -/
theorem ValidTmN.of_app_var {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    {B : Tm Head (n + 1)} (ctx : ValidCtxN M Γ) (validPi : ValidTyN M Γ (.pi A B))
    (typed : Typed M.side.R Γ t (.pi A B))
    (isFun : ∀ {r : Nat} (ς : Sub Head n r), IsFun M.side.roles (Presentation.subst ς t))
    (validApp : ValidTmN M (.snoc Γ A) (.app (Presentation.rename wk t) (.var 0)) B) :
    ValidTmN M Γ t (.pi A B) := by
  have app_subst : ∀ {m : Nat} (a : Tm Head m) (σ : Sub Head n m),
      Presentation.subst (consSub a σ) (.app (Presentation.rename wk t) (.var 0)) =
        .app (Presentation.subst σ t) a := by
    intro m a σ
    simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero]
  refine ⟨validPi, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  have domDen : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (w : Morph ξ ξ' ρ),
      DenN M ξ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A) (Q.dom w) := by
    intro k ξ' ρ w
    have interpA := interprets.dom w
    rw [rename_subst] at interpA
    exact ⟨l, interpA⟩
  have codDen : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k} (w : Morph ξ ξ' ρ)
      {a : Tm Head k} (ha : (Q.dom w).Val a),
      DenN M ξ' (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) B)
        (Q.cod w ha) := by
    intro k ξ' ρ w a ha
    have interpB := interprets.cod w ha
    rw [inst0_rename_subst_liftSub] at interpB
    exact ⟨l, interpB⟩
  -- The realizer instances are typed weak-head normal functions.
  obtain ⟨-, -, -, types⟩ := validPi e
  have typePi := types.left
  obtain ⟨typeA, -⟩ := IsType.pi_parts typePi
  have hX : RedTy M.side.R M.side.roles Δ (Presentation.subst ς (.pi A B))
      (.pi (Presentation.subst ς A) (Presentation.subst (liftSub ς) B)) := RedTy.refl typePi
  have tL : Typed M.side.R Δ (Presentation.subst ς t) (Presentation.subst ς (.pi A B)) :=
    e.typed typed
  have tR : Typed M.side.R Δ (Presentation.subst ς' t) (Presentation.subst ς (.pi A B)) :=
    Typed.convType (typed.substitute (EqSubstN.substMor_right laws ctx e)) types.typeEq.symm
  have star := ValueSide.DenS.star_val laws.value (domDen (Morph.id ξ))
  refine ⟨fun {_ ξ' ρ} w {a b} ha hab => ?_,
    PiPack.real_of_clause Q hX e.formed star ⟨_, .refl tL, isFun ς⟩ ⟨_, .refl tR, isFun ς'⟩
      fun {_ ξ' ρ} w {a} ha {_ Θ ρr} world {s s'} hs => ?_⟩
  · -- Related arguments: the valuation extended by them, with the fresh variable.
    have e' := (EqSubstN.rename laws e w).consVar typeA (domDen w) hab
    have h := (validApp.2 e' (codDen w ha)).1
    rw [app_subst, app_subst] at h
    rw [rename_subst, rename_subst]
    exact h
  · -- Realizers of a valid argument: the valuation extended by them.
    have hs' : ((Q.dom w).real a).rel Θ
        (Presentation.subst (fun i => Presentation.rename ρr (ς i)) A) s s' := by
      rw [← rename_subst]
      exact hs
    have e' := ((EqSubstN.rename laws e w).renameReal world.1 world.2).cons (domDen w)
      ⟨ha, hs'⟩
    have h := (validApp.2 e' (codDen w ha)).2
    rw [app_subst, app_subst, app_subst] at h
    rw [inst0_rename_subst_liftSub, rename_subst, rename_subst, rename_subst]
    exact h

/-- **A closed term is a valid term of its closed type when its full application
to the variables of the telescope is valid**, it is typed at its closed type on
the realizer side, and its partial applications are weak-head normal functions
there. -/
theorem ValidTmN.close : ∀ {n : Nat} (Θ : Ctx Head n) {C : Tm Head n} {f : Tm Head 0},
    ValidTyN M .nil (closeType Θ C) → StructuredN M .nil (closeType Θ C) →
      Typed M.side.R .nil f (closeType Θ C) →
      (∀ {r : Nat} (args : List (Tm Head r)), args.length < n →
        IsFun M.side.roles (appSpine (liftClosed f) args)) →
      ValidTmN M Θ (applyClosed Θ ids (liftClosed f)) C → ValidTmN M .nil f (closeType Θ C)
  | _, .nil, _, f, _, _, _, _, valid => by
      rw [show applyClosed (.nil : Ctx Head 0) ids (liftClosed f) = liftClosed f from rfl,
        liftClosed_zero] at valid
      exact valid
  | _, .snoc Θ A, C, f, validType, partsType, typedF, unsaturated, valid => by
      obtain ⟨ctx, validPi, _⟩ :=
        ValidTyN.close_parts Θ (C := .pi A C) validType partsType
      refine ValidTmN.close Θ (C := .pi A C) validType partsType typedF
        (fun args short => unsaturated args (Nat.lt_succ_of_lt short))
        (ValidTmN.of_app_var laws ctx.valid validPi ?_ (fun ς => ?_) ?_)
      · have h := Typed.telescope_apply (X := .pi A C) (substMor_ids Θ)
          (Typed.liftClosed (Δ := Θ) typedF)
        rwa [subst_ids] at h
      · rw [applyClosed_subst, subst_liftClosed, applyClosed_eq_appSpine]
        exact unsaturated _ (by rw [telescopeArgs_length]; exact Nat.lt_succ_self _)
      · rw [← applyClosed_snoc_ids]
        exact valid

/-- **A term is valid when it computes on the value side to a valid term**
under every substitution, it is typed on the realizer side, and its realizer
instances compute to those of the valid term by a root step of the realizer
side. -/
theorem ValidTmN.of_red {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (ctx : ValidCtxN M Γ)
    (red : ∀ {m : Nat} (σ : Sub Head n m),
      WhRed M.rules M.roles (Presentation.subst σ t) (Presentation.subst σ u))
    (realStep : ∀ {r : Nat} (ς : Sub Head n r),
      M.side.R.computation.step (Presentation.subst ς t) (Presentation.subst ς u))
    (typed : Typed M.side.R Γ t A) (valid : ValidTmN M Γ u A) : ValidTmN M Γ t A := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨h, hreal⟩ := rel e den
  have expansive := ValueSide.DenS.expansive laws.value den
  refine ⟨expansive.left (red σ) (expansive.right (red σ') h), ?_⟩
  have same : P.real (Presentation.subst σ t) = P.real (Presentation.subst σ u) :=
    ValueSide.DenS.real_eq_of_rel laws.value den
      (expansive.left (red σ) (ValueSide.DenS.refl_left laws.value den h))
  rw [same]
  obtain ⟨-, -, -, types⟩ := validA e
  obtain ⟨tu, tu'⟩ := (P.real _).typed hreal
  have tt : Typed M.side.R Δ (Presentation.subst ς t) (Presentation.subst ς A) := e.typed typed
  have tt' : Typed M.side.R Δ (Presentation.subst ς' t) (Presentation.subst ς A) :=
    Typed.convType (typed.substitute (EqSubstN.substMor_right laws ctx e)) types.typeEq.symm
  exact (P.real _).expand (RedTm.root (realStep ς) tt tu) (RedTm.root (realStep ς') tt' tu')
    hreal

end Laws

/-- **A constant defined by one equation `f x₁ ⋯ x_k ⟶ rhs` is a valid term of
its declared type**, when its declared type and right-hand side are typed in a
package sound for the model: its full application computes on the value side
to the right-hand side, which is valid by the fundamental lemma of that package,
and on the realizer side it is declared at its type, computes to the right-hand
side by a root step, and its partial applications are weak-head normal
functions. -/
theorem ValidTmN.definition {R₀ : Rules Head} (sound₀ : TypedSoundN R₀ M) {f : DeclName}
    {k : Nat} {Θ : Ctx Head k} {C rhs : Tm Head k}
    (typed : ∃ w, R₀.isUniverse w ∧ Typed R₀ .nil (closeType Θ C) (.head w))
    (body : Typed R₀ Θ rhs C)
    (declared : Typed M.side.R .nil (.const f) (closeType Θ C))
    (role : ∃ inspect, M.side.roles f = .computes k inspect)
    (rule : ∀ {n : Nat} (σ : Sub Head k n),
      WhRed M.rules M.roles (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs))
    (realRule : ∀ {n : Nat} (σ : Sub Head k n),
      M.side.R.computation.step (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs)) :
    ValidTmN M .nil (.const f) (closeType Θ C) := by
  have laws := sound₀.laws
  obtain ⟨w, hw, typedC⟩ := typed
  obtain ⟨validC, partsC, _⟩ := Derivable.validTN sound₀ typedC trivial
  have validType : ValidTyN M .nil (closeType Θ C) :=
    validC.validTy (sound₀.isUniverse hw) (sound₀.isUniverse' hw)
  obtain ⟨ctx, _, _⟩ := ValidTyN.close_parts Θ validType partsC
  obtain ⟨inspect, hrole⟩ := role
  have typedApp : Typed M.side.R Θ (applyClosed Θ ids (liftClosed (.const f))) C := by
    have h := Typed.telescope_apply (X := C) (substMor_ids Θ) (Typed.liftClosed (Δ := Θ) declared)
    rwa [subst_ids] at h
  refine ValidTmN.close laws Θ validType partsC declared
    (fun args short => .inr (.inr ⟨f, args, k, .inr ⟨inspect, hrole⟩, short, rfl⟩))
    (ValidTmN.of_red laws ctx.valid (fun σ => ?_) (fun ς => ?_) typedApp
      (Typed.validN sound₀ body ctx))
  · rw [applyClosed_subst]
    exact rule _
  · rw [applyClosed_subst]
    exact realRule _

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
