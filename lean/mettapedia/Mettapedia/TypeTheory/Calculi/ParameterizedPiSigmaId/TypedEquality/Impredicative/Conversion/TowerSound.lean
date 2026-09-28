import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.TowerModel

/-!
# The fundamental lemma at the conversion model of the universe tower

The universe tower is sound for its conversion model (`Tower.typedSoundN`): its
universe rules are the model's on both sides, and it has no root step and no
constant. Read through the fundamental lemma:

* **Escape.** The β-equal terms `(λx. x) U₀` and `U₀` are related by the
  generic equality of the realizer side (`Tower.beta_escape`), while the
  universes `U₀` and `U₁` are not (`Tower.U0_U1_not_convertible`): they are not
  even typed-equal in `U₂`, since the fundamental lemma would give them one pack
  in the model, while `U₁`'s pack relates `U₀` to itself and `U₀`'s does not
  (`Tower.U0_U1_not_validEq`).
* **An unsound root step.** The tower with a root step from `U₀` to `U₁`
  (`Tower.collapse`) is not sound for the model (`Tower.collapse_not_typedSoundN`):
  the step makes the two universes typed-equal in `U₂`.
* **Realizers along renamings.** Along a morphism of worlds a renamed valid
  value has every realizer of the value (`Tower.holds_realsRenamed`). Along a
  renaming that changes the generic of a variable it need not: `holds x` read
  with the generic `top` is realized by `top`, which relates `U₀` to itself at
  `U₁`, and read with the generic `bot` by `bot`, which does not
  (`Tower.holds_not_realsRenamed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open Consistency (Carrier World Truth Morph)

namespace Tower

/-! ## Soundness -/

/-- **The universe tower is sound for its conversion model**: its universe rules
are the model's on both sides, and it has no root step and no constant. -/
theorem typedSoundN : TypedSoundN rules model where
  laws := model_laws
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := id
  isUniverse' := id
  join' := id
  cumulative' := id
  headEq' := id
  root := fun step => nomatch step
  constants := fun declared => nomatch declared

/-! ## Two universes -/

/-- The empty valuation of the empty context. -/
theorem nil_eqSubst :
    EqSubstN model .nil World.closed (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) .nil
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) :=
  CtxFormed.nil

/-- **`U₀` and `U₁` are not validly equal in `U₂`**: validly equal types of a
universe have one pack, while `U₁`'s pack relates `U₀` to itself and `U₀`'s pack
does not. -/
theorem U0_U1_not_validEq : ¬ ValidEqN model .nil (.head 0) (.head 1) (.head 2) := by
  intro equal
  have laws := model_laws.value
  obtain ⟨P, h₀, h₁⟩ := equal.den (u := 2) trivial nil_eqSubst
  have p₀ := ValueSide.DenS.sort_inv laws (u := 0) trivial h₀
  have p₁ := ValueSide.DenS.sort_inv laws (u := 1) trivial h₁
  have typing : Typed rules (.nil : Ctx Nat 0) (.head 0) (.head 1) := .headType rfl
  have related : (ValueSide.universeAt model.value (model.value.levels.level 1) World.closed).rel
      (.head 0) (.head 0) :=
    (ValidTmN.universe (Typed.validN typedSoundN typing trivial) (u := 1) trivial
      nil_eqSubst).1
  rw [← p₁, p₀] at related
  obtain ⟨Q, interp, -, -⟩ := related (Morph.id World.closed)
  exact U0_not_interp_zero World.closed Q interp

/-- **`U₀` and `U₁` are not typed-equal in `U₂`**, by the fundamental lemma. -/
theorem U0_U1_not_equal : ¬ Equal rules (.nil : Ctx Nat 0) (.head 0) (.head 1) (.head 2) :=
  fun equal => U0_U1_not_validEq (Equal.validN typedSoundN equal trivial)

/-- **The generic equality of the tower does not relate `U₀` and `U₁`** in `U₂`. -/
theorem U0_U1_not_convertible : ¬ side.E.convTm (.nil : Ctx Nat 0) (.head 0) (.head 1) (.head 2) :=
  U0_U1_not_equal

/-- The identity function of `U₁`. -/
theorem idU1_typed : Typed rules (.nil : Ctx Nat 0) (.pi (.head 1) (.head 1)) (.head 2) :=
  .piForm (.headType rfl) trivial (.headType rfl) trivial (show 2 = max 2 2 from rfl)

/-- **Escape**: the β-equal terms `(λx. x) U₀` and `U₀` are related by the generic
equality of the realizer side in `U₁`. -/
theorem beta_escape :
    side.E.convTm (.nil : Ctx Nat 0) (.app (.lam (.var 0)) (.head 0)) (.head 0) (.head 1) :=
  Equal.escapeN typedSoundN .nil
    (Derivable.betaPi (B := .head 1) idU1_typed trivial (.var 0) (.headType rfl))

/-! ## An unsound root step -/

/-- The root step from `U₀` to `U₁`. -/
def collapseStep : RootComputation Nat where
  step := fun l r => l = .head 0 ∧ r = .head 1
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The universe tower with a root step from `U₀` to `U₁`. -/
def collapse : Rules Nat := { rules with computation := collapseStep }

/-- The step makes `U₀` and `U₁` typed-equal in `U₂`. -/
theorem collapse_equal : Equal collapse (.nil : Ctx Nat 0) (.head 0) (.head 1) (.head 2) :=
  .root ⟨rfl, rfl⟩ (Derivable.cumul (.headType rfl) (show 1 ≤ 2 by decide)) (.headType rfl)

/-- **A package with an unsound root step is not sound for the model**: the tower
with a root step from `U₀` to `U₁` would make the two universes validly equal. -/
theorem collapse_not_typedSoundN : ¬ TypedSoundN collapse model :=
  fun sound => U0_U1_not_validEq (Equal.validN sound collapse_equal trivial)

/-! ## Realizers along renamings -/

/-- A world with one generic code, read as the candidate `X`. -/
def codeWorld (X : ECand side) : World model.reading 1 := fun _ => ⟨.prop, X⟩

/-- The decoding of the variable, read in a world with one generic code, is the
decoding pack of the generic's candidate. -/
theorem holds_interp (X : ECand side) (l : Nat) :
    NInterp model l (codeWorld X) (.app (.const holdsName) (.var 0))
      (ValueSide.holdsPack model.value 1 X) :=
  ValueSide.SInterp.holds .refl (.generic (i := 0) (args := []) .refl .done)

/-- `top` relates `U₀` to itself at `U₁`. -/
theorem top_U0 : (ECand.top side).rel (.nil : Ctx Nat 0) (.head 1) (.head 0) (.head 0) :=
  ⟨.headType rfl, .headType rfl, .refl (.headType rfl)⟩

/-- **Along a morphism of worlds, a renamed valid value has every realizer of the
value**: here along the weakening past a new generic. -/
theorem holds_realsRenamed (X : ECand side) (g : Consistency.Gen model.reading) :
    ∃ P', NInterp model 0 ((codeWorld X).snoc g)
        (Presentation.rename wk (.app (.const holdsName) (.var 0))) P' ∧
      RealsRenamed (ValueSide.holdsPack model.value 1 X) wk P' := by
  obtain ⟨P', interp', -, reals⟩ :=
    NInterp.real_rename model_laws (holds_interp X 0) (Morph.wk (codeWorld X) g)
  exact ⟨P', interp', reals⟩

/-- **Along a renaming that changes the generic of a variable, a value's
realizers need not be carried**: `holds x`, read with the generic `top`, is
realized by `top`, which relates `U₀` to itself at `U₁`; read with the generic
`bot` it is realized by `bot`, which does not. The identity is no morphism
between the two worlds. -/
theorem holds_not_realsRenamed :
    ¬ Morph (codeWorld (ECand.top side)) (codeWorld (ECand.bot side)) idRen ∧
      ¬ RealsRenamed (ValueSide.holdsPack model.value 1 (ECand.top side)) idRen
        (ValueSide.holdsPack model.value 1 (ECand.bot side)) := by
  refine ⟨fun w => ?_, fun reals => ?_⟩
  · have same : ECand.bot side = ECand.top side := eq_of_heq (Sigma.mk.inj (w 0)).2
    have h := top_U0
    rw [← same] at h
    exact U0_not_bot h
  · exact U0_not_bot (reals (a := .const daimonName) trivial top_U0)

end Tower

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
