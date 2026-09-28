import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Coherence

/-!
# Root computations in the consistency model

A root step of the object package is read in the model in one of two ways:

* as a step of the model's own computation, which is closed under
  substitution, so the two sides of the step are related by expansion;
* as a decoding of a code, `holds c ⟶ D`, where the model keeps `holds c`
  rigid. Both sides are type-like terms. In a universe they have one
  interpretation at every world, because the decoding has the partial
  equivalence of `holds c`; elsewhere every partial equivalence that relates
  each of them to itself relates them to each other.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-- The decoders of an object package are the model's codes: the same decoder
and implication, and quantifier and equation instances over interpretable
carriers whose closed types are the carriers' types. -/
structure Decodes (M : Model Head L) (D : Decoders Head) : Prop where
  holds : D.holds = M.holds
  imp : D.imp = M.imp
  all : ∀ {a : DeclName} {T : Tm Head 0}, D.allCarrier a = some T →
    ∃ (k : Kind) (A : Carrier k), M.allCarrier a = some ⟨k, A⟩ ∧ A.Interpretable M ∧
      T = A.term M
  eq : ∀ {e : DeclName} {T : Tm Head 0}, D.eqCarrier e = some T →
    ∃ (k : Kind) (A : Carrier k), M.eqCarrier e = some ⟨k, A⟩ ∧ A.Interpretable M ∧
      T = A.term M

/-- A root step of an object package, read in the model: a step of the
model's computation, or a decoding. -/
def ModelRoot (M : Model Head L) (D : Decoders Head) {n : Nat} (l r : Tm Head n) : Prop :=
  M.rules.computation.step l r ∨ DecoderStep D l r

theorem DecoderStep.typeLike_left {D : Decoders Head} (decodes : Decodes M D) {n : Nat}
    {x y : Tm Head n} (step : DecoderStep D x y) : TypeLike M x := by
  cases step <;> rw [decodes.holds] <;> exact .holds _

theorem DecoderStep.typeLike_right {D : Decoders Head} {n : Nat} {x y : Tm Head n}
    (step : DecoderStep D x y) : TypeLike M y := by
  cases step with
  | imp => exact .pi _ _
  | all => exact .pi _ _
  | eq => exact .id _ _ _

section Laws

variable (laws : M.Laws)
include laws

/-- The interpretation of `holds c` is the truth of `c`. -/
theorem InterpAt.holds_inv {l : L} {n : Nat} {ξ : World M.reading n} {c : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ (.app (.const M.holds) c) R) :
    R = (fun _ _ => ∃ P, Truth M.reading ξ c P ∧ P) ∧ ∃ P, Truth M.reading ξ c P := by
  have normal := laws.whnf_holds c
  cases interp with
  | holds red good =>
      cases WhRed.of_whnf normal red
      exact ⟨rfl, good⟩
  | sort _ _ red => cases WhRed.of_whnf normal red
  | ground _ red => cases WhRed.of_whnf normal red
  | pi red => cases WhRed.of_whnf normal red
  | sigma red => cases WhRed.of_whnf normal red
  | ident red => cases WhRed.of_whnf normal red
  | num red => cases WhRed.of_whnf normal red
  | prop red => cases WhRed.of_whnf normal red
  | rigid red _ _ notHolds =>
      exact absurd (appSpine_const_eq_app (WhRed.of_whnf normal red)).1 notHolds

/-- A decoding has the partial equivalence of `holds` of its code. -/
theorem decoder_coherent {D : Decoders Head} (decodes : Decodes M D) {l : L} {n : Nat}
    {ξ : World M.reading n} {x y : Tm Head n} (step : DecoderStep D x y) {R₁ R₂ : Rel Head n}
    (hx : InterpAt M l ξ x R₁) (hy : InterpAt M l ξ y R₂) : R₁ = R₂ := by
  cases step with
  | imp p q =>
      rw [decodes.holds, decodes.imp] at hx
      rw [decodes.holds] at hy
      obtain ⟨rfl, _, truth⟩ := InterpAt.holds_inv laws hx
      obtain ⟨_, _, hp, hq, _⟩ := Truth.imp_inv laws.reading truth
      exact (holds_imp_coherent laws hp hq hy).symm
  | all carrier f =>
      obtain ⟨_, C, carrierM, hC, rfl⟩ := decodes.all carrier
      rw [decodes.holds] at hx hy
      obtain ⟨rfl, _, truth⟩ := InterpAt.holds_inv laws hx
      obtain ⟨_, read, _⟩ := Truth.all_inv laws.reading carrierM truth
      exact (holds_all_coherent laws carrierM hC read hy).symm
  | eq carrier x y =>
      obtain ⟨_, C, carrierM, hC, rfl⟩ := decodes.eq carrier
      rw [decodes.holds] at hx
      obtain ⟨rfl, _, truth⟩ := InterpAt.holds_inv laws hx
      obtain ⟨_, _, readX, readY, _⟩ := Truth.eq_inv laws.reading carrierM truth
      exact (holds_eq_coherent laws carrierM hC readX readY hy).symm

/-- A partial equivalence of the model that relates two type-like terms each to
itself relates them to each other, given that it does so where it is the
partial equivalence of a universe. -/
theorem Interp.typeLike_sort {l : L} {below : L → IRel M.reading}
    (belowStuck : ∀ k {n : Nat} {ξ : World M.reading n} {x : Tm Head n} {R' : Rel Head n},
      Stuck M x → ¬ below k ξ x R')
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R)
    {x y : Tm Head n} (lx : TypeLike M x) (ly : TypeLike M y)
    (sort : ∀ k, k < l → R = universeRel (below k) ξ → R x y) (hxx : R x x) (hyy : R y y) :
    R x y := by
  cases interp with
  | sort _ level _ => exact sort _ level rfl
  | ground _ _ => trivial
  | pi _ P _ codInterp _ =>
      intro _ _ _ w a b ha _
      exact Interp.stuck laws belowStuck (codInterp w ha) (.appLike a (lx.rename _))
        (.appLike b (ly.rename _)) (hxx w ha ha)
  | sigma _ P domInterp codInterp _ =>
      obtain ⟨hp, hd, hc⟩ := hxx
      exact ⟨hp, Interp.stuck laws belowStuck (domInterp (Morph.id ξ)) (.fstLike lx)
          (.fstLike ly) hd,
        Interp.stuck laws belowStuck (codInterp (Morph.id ξ) hp) (.sndLike lx) (.sndLike ly) hc⟩
  | ident _ _ _ _ _ => exact hxx
  | num _ =>
      obtain ⟨_, hk, _⟩ := hxx
      exact absurd hk (lx.not_numVal laws)
  | prop _ =>
      obtain ⟨_, hP, _⟩ := hxx
      exact absurd hP (lx.not_truth laws)
  | holds _ _ => exact hxx
  | rigid _ _ _ _ => trivial

/-- Heads that are the same up to the package's head equality have one
interpretation at each level. -/
theorem head_same {h h' : Head} (same : M.rules.headEq h h') {l : L} {n : Nat} {ξ : World M.reading n}
    {R₁ R₂ : Rel Head n} (first : InterpAt M l ξ (.head h) R₁) (second : InterpAt M l ξ (.head h') R₂) :
    R₁ = R₂ := by
  obtain ⟨universes, level⟩ := M.levels.headEq_level same
  rcases InterpAt.head_inv laws first with ⟨hu, _, rfl⟩ | ⟨hu, rfl⟩ <;>
    rcases InterpAt.head_inv laws second with ⟨hu', _, rfl⟩ | ⟨hu', rfl⟩
  · rw [level]
  · exact absurd (universes.mp hu) hu'
  · exact absurd (universes.mpr hu') hu
  · rfl

/-- Heads that are the same up to the package's head equality are validly
equal wherever each is a valid term. -/
theorem ValidEq.headEq {n : Nat} {Γ : Ctx Head n} {h h' : Head} {A : Tm Head n}
    (same : M.rules.headEq h h') (valid : ValidTm M Γ (.head h) A)
    (valid' : ValidTm M Γ (.head h') A) : ValidEq M Γ (.head h) (.head h') A := by
  refine ⟨valid, valid', fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, rel⟩ := valid
  obtain ⟨_, rel'⟩ := valid'
  have hxx := rel e den
  have hyy := rel' e den
  obtain ⟨L, interp⟩ := den
  refine Interp.typeLike_sort laws (levelsBelow_stuck laws) interp (.head h) (.head h')
    (fun k lt hk => ?_) hxx hyy
  subst hk
  rw [universeRel_levelsBelow lt] at hxx hyy ⊢
  intro _ _ _ w
  obtain ⟨R₁, hx, _⟩ := hxx w
  obtain ⟨R₂, hy, _⟩ := hyy w
  refine ⟨R₁, hx, ?_⟩
  rw [head_same laws same hx hy]
  exact hy

/-- The two sides of a root step of the object package, read in the model, are
validly equal wherever each is a valid term. -/
theorem ValidEq.root {D : Decoders Head} (decodes : Decodes M D) {n : Nat}
    {Γ : Ctx Head n} {l r A : Tm Head n} (root : ModelRoot M D l r)
    (validL : ValidTm M Γ l A) (validR : ValidTm M Γ r A) : ValidEq M Γ l r A := by
  refine ⟨validL, validR, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, relL⟩ := validL
  obtain ⟨_, relR⟩ := validR
  have hl := relL e den
  have hr := relR e den
  rcases root with step | step
  · exact Den.expandLeft den
      (Relation.ReflTransGen.single (WhStep.root (M.rules.computation.substitute σ step))) hr
  · obtain ⟨L, interp⟩ := den
    refine Interp.typeLike_sort laws (levelsBelow_stuck laws) interp
      (DecoderStep.typeLike_left decodes (step.substitute σ))
      (DecoderStep.typeLike_right (step.substitute σ'))
      (fun k lt hk => ?_) (Den.refl_left laws ⟨L, interp⟩ hl) (Den.refl_right laws ⟨L, interp⟩ hr)
    subst hk
    rw [universeRel_levelsBelow lt] at hl hr ⊢
    intro _ _ ρ w
    obtain ⟨R₁, hx, hx'⟩ := hl w
    obtain ⟨R₂, _, hy⟩ := hr w
    refine ⟨R₁, hx, ?_⟩
    rw [decoder_coherent laws decodes ((step.substitute σ').rename ρ) hx' hy]
    exact hy

end Laws

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
