import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringNullary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringCensusControls

/-!
# The inversion row is inhabited: a pattern with one local

* **Unary patterns** (`inversionRow_unary`): `λ x. F x ≐ λ x. t` for the newest metavariable `F : Π (x : D'). C'`,
  annotated at `Π (x : D). C` with `D` the weakening of `D'` and `C` convertible with `C'` at `x`, with `t` normal and
  mentioning only `x` and the declarations older than `F`, is in the inversion row. The opening reads `F x`; each
  spine of length one of the annotation and of `F`'s type is the literal Π prefix; the renaming of the pattern sends
  `F`'s binder to the local `x` and every older declaration to itself, so it is the identity, and the agreement of
  declared types is the agreement of `D` with `D'` and of `C` with `C'`.
* **The tower store** `λ x. F x ≐ λ x. Π x A` over `A : U0, F : U0 → U0` (`inversionStore`): it is in the fragment and
  in the inversion row through every view of `F` (`inversion_row`), so the firing round is not stuck on it from some
  budget on (`inversion_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking ContextualDependentExecutableDiscovery
open ContextualDependentPiSpine ContextualDependentDynamicFragment ContextualDependentScope ContextualDependentGeneralPattern

section General

variable {Head : Type} {rules : Rules Head}

/-- A spine of length zero is the empty one. -/
theorem spine_eq_stop {Γ : Context rules} {T : TypeOver Γ} (spine : Spine T) (zero : spine.length = 0) :
    spine = .stop T := by
  cases spine with
  | stop => rfl
  | bind shape rest => exact absurd zero (Nat.succ_ne_zero _)

/-- **The unary inversion row**: `λ x. F x ≐ λ x. t` for the newest metavariable `F : Π (x : D'). C'`, at
`Π (x : D). C` with `D` the weakening of `D'` and `C` convertible with `C'`, with `t` normal and mentioning only `x`
and the declarations older than `F`. -/
theorem inversionRow_unary (empty : rules.computation = RootComputation.empty) {Γ : Context rules}
    {type : TypeOver Γ} (equation : Equation (TotalTerm (extend Γ type)))
    {D' : Tm Head Γ.arity} {C' : Tm Head (Γ.arity + 1)} {D : Tm Head (Γ.arity + 1)} {C : Tm Head (Γ.arity + 1 + 1)}
    {r : Tm Head (Γ.arity + 1 + 1)}
    (typeCode : type.code = .pi D' C') (annotationCode : equation.1.1.code = .pi D C)
    (left : equation.1.2.code =
      .lam (.app (.var ⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩) (.var ⟨0, Nat.succ_pos _⟩)))
    (right : equation.2.2.code = .lam r)
    (domain : D = Presentation.rename wk D')
    (codomain : TypeEq rules (.snoc (.snoc Γ.raw type.code) D) C (Presentation.rename (liftRen wk) C'))
    (normal : Normal rules r)
    (avoids : ∀ index ∈ r.support, index.val = 0 ∨ 1 < index.val) :
    InversionRow equation := by
  rcases equation with ⟨⟨annotationType, ⟨leftCode, leftTyped⟩⟩, ⟨rightType, ⟨rightCode, rightTyped⟩⟩⟩
  dsimp only at annotationCode left right
  subst left right
  intro opened reduct leftSteps leftNormal rightSteps rightNormal
  have appNormal : Normal rules (.app (.var ⟨1, by omega⟩) (.var ⟨0, by omega⟩) : Tm Head (Γ.arity + 1 + 1)) :=
    (ContextualDependentNormalizing.normal_iff_step_none empty _).mpr rfl
  have leftSame : opened = (.app (.var ⟨1, by omega⟩) (.var ⟨0, by omega⟩) : Tm Head (Γ.arity + 1 + 1)) :=
    normal_reduct_unique empty (ContextualDependentCensus.openCode_star (R := rules) _ 1) appNormal leftSteps
      leftNormal
  have rightSame : reduct = r :=
    normal_reduct_unique empty (ContextualDependentCensus.openCode_star (R := rules) _ 1) normal rightSteps
      rightNormal
  refine ⟨_, [⟨0, Nat.succ_pos _⟩], by rw [leftSame]; rfl, by rfl, ?_, List.nodup_singleton _, ?_, ?_⟩
  · intro argument member
    rw [List.mem_singleton.mp member]
    exact Nat.zero_lt_one
  · intro index member
    rw [rightSame] at member
    rcases avoids index member with zero | above
    · exact Or.inr (List.mem_singleton.mpr (Fin.ext zero))
    · exact Or.inl above
  · intro scope spine same args localsSame
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = argRen (lifted spine) scope idRen
        (fun position => args (spine.localReindexEquiv _ position)) := ⟨_, rfl⟩
    rw [← hρ]
    cases scope with
    | stop => exact absurd same Nat.zero_ne_one
    | bind shape rest =>
        obtain rfl := spine_eq_stop rest (Nat.succ.inj same)
        cases spine with
        | stop => simp [ContextualDependentPatternSolver.locals] at localsSame
        | bind shape' rest' =>
            have split := List.cons.inj localsSame
            have restLocals : ContextualDependentPatternSolver.locals rest' = [] :=
              List.map_eq_nil_iff.mp (List.map_eq_nil_iff.mp split.2)
            have restLength : rest'.length = 0 := by
              rw [← length_locals rest', restLocals]
              rfl
            obtain rfl := spine_eq_stop rest' restLength
            obtain ⟨d₁, c₁⟩ := Tm.pi.inj (shape.code.symm.trans annotationCode)
            obtain ⟨d₂, c₂⟩ := Tm.pi.inj (shape'.code.symm.trans typeCode)
            subst d₁ c₁ d₂ c₂
            have ρid : ∀ index, ρ index = index := by
              intro index
              rw [hρ]
              refine Fin.cases ?_ (fun previous => ?_) index
              · exact split.1.trans (Fin.ext rfl)
              · rfl
            have ρeq : ρ = fun index => index := funext ρid
            subst ρeq
            refine ⟨?_, codomain⟩
            show CtxRen (.snoc (.snoc Γ.raw shape'.whole.code) (subst projection shape'.domain.code))
              (.snoc (.snoc Γ.raw shape'.whole.code) shape.domain.code) (fun index => index)
            rw [subst_projection, ← domain]
            exact CtxRen.id _

end General

namespace Controls

open ContextualDependentEta ContextualDependentWorklist

theorem endo_code : endo.code = .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 typeContext
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).get (by decide +kernel)).property

theorem endoG_code : endoG.code = .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withG
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).get (by decide +kernel)).property

theorem inversionStore_length : inversionStore.length = 1 := rfl

def inversionEquation : Equation (TotalTerm withG) :=
  inversionStore.head (List.ne_nil_of_length_pos (by rw [inversionStore_length]; decide))

theorem inversionStore_eq : inversionStore = [inversionEquation] := rfl

/-- **`λ x. F x ≐ λ x. Π x A` is in the dynamic pattern fragment.** -/
theorem inversion_in_fragment : InFragmentStore inversionStore := by
  rw [inversionStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl inversionEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem inversion_body_normal :
    Normal (LevelTower.rules Nat) (.pi (.var 0) (.var 3) : Tower.Tm 3) :=
  (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr rfl

theorem inversion_body_avoids :
    ∀ index ∈ (.pi (.var 0) (.var 3) : Tower.Tm 3).support, index.val = 0 ∨ 1 < index.val := by
  decide +kernel

/-- The codomain `U0` of the annotation is a type under its binder. -/
theorem inversion_codomain :
    TypeEq setting.R
      (.snoc (.snoc typeContext.raw (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
        (.head (.sort Tower.zero)))
      (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) := by
  have isType := endoG.isType
  change IsType setting.R (.snoc typeContext.raw endo.code) endoG.code at isType
  rw [endo_code, endoG_code] at isType
  exact IsType.refl (IsType.pi_parts isType).2

/-- **`λ x. F x ≐ λ x. Π x A` is in the inversion row** through every view of `F`. -/
theorem inversion_row :
    ∀ view : Newest (S := setting) withG, InversionRow (view.same ▸ inversionEquation) := by
  rintro ⟨⟨arity, raw, formed⟩, ⟨code, level, witness, typed⟩, same⟩
  injection same with arityEq rawEq
  have arityEq' : typeContext.arity = arity := Nat.succ.inj arityEq
  subst arityEq'
  have rawEq' := eq_of_heq rawEq
  cases rawEq'
  exact inversionRow_unary rfl _ (D' := .head (.sort Tower.zero)) (C' := .head (.sort Tower.zero))
    (D := .head (.sort Tower.zero)) (C := .head (.sort Tower.zero)) (r := .pi (.var 0) (.var 3))
    rfl endoG_code rfl rfl rfl inversion_codomain inversion_body_normal inversion_body_avoids

/-- The newest declaration `U0 → U0` is normal. -/
theorem inversion_newest_normal :
    Normal (LevelTower.rules Nat) (Ctx.lookup withG.raw ⟨0, Nat.succ_pos _⟩) := by
  change Normal (LevelTower.rules Nat) (Presentation.rename wk endo.code)
  rw [endo_code]
  exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr rfl

/-- **The firing round is not stuck on `λ x. F x ≐ λ x. Π x A`** from some budget on, by the firing theorem on the
inversion row. -/
theorem inversion_fires :
    ∃ bound, ∀ larger, bound ≤ larger → firingTower.round larger inversionStore ≠ .stuck :=
  firingRound_fires_inversion (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique inversionStore
    (by rw [inversionStore_eq]; exact List.mem_singleton_self _)
    (inversion_in_fragment _ (by rw [inversionStore_eq]; exact List.mem_singleton_self _))
    (Nat.succ_pos _) inversion_newest_normal inversion_row

end Controls

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
