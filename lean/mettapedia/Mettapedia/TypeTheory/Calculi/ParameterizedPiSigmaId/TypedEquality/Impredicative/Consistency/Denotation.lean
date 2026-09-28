import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Validity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.StuckRel

/-!
# Laws of denotations

A type's denotation is its interpretation at some level. Interpretations are
cumulative, so the denotation is unique; it is a partial equivalence, closed
under weak-head expansion on either side, and it follows world morphisms. A
denotation of a type former is given by the clause of that former.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

section Laws

variable (laws : M.Laws)
include laws

theorem Den.deterministic {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R R' : Rel Head n}
    (first : Den M ξ A R) (second : Den M ξ A R') : R = R' := by
  obtain ⟨l, hl⟩ := first
  obtain ⟨l', hl'⟩ := second
  exact InterpAt.deterministic laws (hl.cumul (le_max_left l l')) (hl'.cumul (le_max_right l l'))

theorem Den.symm {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {t u : Tm Head n} (h : R t u) : R u t := by
  obtain ⟨_, hl⟩ := den
  exact hl.symm laws h

theorem Den.trans {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {t u v : Tm Head n} (h : R t u) (h' : R u v) : R t v := by
  obtain ⟨_, hl⟩ := den
  exact hl.trans laws h h'

theorem Den.refl_left {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {t u : Tm Head n} (h : R t u) : R t t :=
  den.trans laws h (den.symm laws h)

theorem Den.refl_right {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {t u : Tm Head n} (h : R t u) : R u u :=
  den.trans laws (den.symm laws h) h

theorem Den.rename {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ R', Den M ξ' (Presentation.rename ρ A) R' ∧
      ∀ {a b : Tm Head n}, R a b → R' (Presentation.rename ρ a) (Presentation.rename ρ b) := by
  obtain ⟨l, hl⟩ := den
  obtain ⟨R', h', map⟩ := hl.rename laws w
  exact ⟨R', ⟨l, h'⟩, map⟩

end Laws

theorem Den.expandLeft {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (den : Den M ξ A R)
    {t t' u : Tm Head n} (red : WhRed M.rules M.roles t t') (h : R t' u) : R t u := by
  obtain ⟨_, hl⟩ := den
  exact hl.expandLeft red h

theorem Den.expandRight {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (den : Den M ξ A R) {t u u' : Tm Head n} (red : WhRed M.rules M.roles u u') (h : R t u') :
    R t u := by
  obtain ⟨_, hl⟩ := den
  exact hl.expandRight red h

theorem Den.expand {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n}
    (red : WhRed M.rules M.roles A A') (den : Den M ξ A' R) : Den M ξ A R := by
  obtain ⟨l, hl⟩ := den
  exact ⟨l, Interp.expand red hl⟩

/-! ## Denotations of type formers -/

section Inversion

variable (laws : M.Laws)
include laws

theorem InterpAt.pi_inv {l : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {R : Rel Head n} (interp : InterpAt M l ξ (.pi A B) R) :
    ∃ P : PiRel Head ξ, R = P.rel ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        InterpAt M l ξ' (Presentation.rename ρ A) (P.dom w)) ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
        (ha : P.dom w a a),
        InterpAt M l ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (P.cod w ha)) ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a b : Tm Head m}
        (ha : P.dom w a a) (hb : P.dom w b b), P.dom w a b → P.cod w ha = P.cod w hb) := by
  cases interp with
  | pi red P domInterp codInterp codRespect =>
      cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
      exact ⟨P, rfl, domInterp, codInterp, codRespect⟩
  | sort _ _ red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | ground _ red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | sigma red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | ident red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | num red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | prop red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | holds red => cases WhRed.of_whnf (pi_whnf laws.shape _ _) red
  | rigid red =>
      exact absurd (WhRed.of_whnf (pi_whnf laws.shape _ _) red) appSpine_const_ne_pi

theorem InterpAt.sigma_inv {l : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {R : Rel Head n} (interp : InterpAt M l ξ (.sigma A B) R) :
    ∃ P : PiRel Head ξ, R = P.pairRel ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        InterpAt M l ξ' (Presentation.rename ρ A) (P.dom w)) ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
        (ha : P.dom w a a),
        InterpAt M l ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (P.cod w ha)) ∧
      (∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a b : Tm Head m}
        (ha : P.dom w a a) (hb : P.dom w b b), P.dom w a b → P.cod w ha = P.cod w hb) := by
  cases interp with
  | sigma red P domInterp codInterp codRespect =>
      cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
      exact ⟨P, rfl, domInterp, codInterp, codRespect⟩
  | sort _ _ red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | ground _ red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | pi red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | ident red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | num red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | prop red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | holds red => cases WhRed.of_whnf (sigma_whnf laws.shape _ _) red
  | rigid red =>
      exact absurd (WhRed.of_whnf (sigma_whnf laws.shape _ _) red) appSpine_const_ne_sigma

theorem InterpAt.id_inv {l : L} {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ (.id A a b) R) :
    ∃ RA, R = (fun _ _ => RA a b) ∧ InterpAt M l ξ A RA ∧ RA a a ∧ RA b b := by
  cases interp with
  | ident red RA tyInterp lhsRefl rhsRefl =>
      cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
      exact ⟨RA, rfl, tyInterp, lhsRefl, rhsRefl⟩
  | sort _ _ red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | ground _ red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | pi red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | sigma red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | num red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | prop red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | holds red => cases WhRed.of_whnf (id_whnf laws.shape _ _ _) red
  | rigid red =>
      exact absurd (WhRed.of_whnf (id_whnf laws.shape _ _ _) red) appSpine_const_ne_id

theorem InterpAt.head_inv {l : L} {n : Nat} {ξ : World M.reading n} {u : Head} {R : Rel Head n}
    (interp : InterpAt M l ξ (.head u) R) :
    (M.rules.isUniverse u ∧ M.levels.level u < l ∧
      R = universeRel (levelsBelow M l (M.levels.level u)) ξ) ∨
    (¬ M.rules.isUniverse u ∧ R = fun _ _ => True) := by
  cases interp with
  | sort isUniverse level red =>
      cases WhRed.of_whnf (head_whnf laws.shape _) red
      exact .inl ⟨isUniverse, level, rfl⟩
  | ground notUniverse red =>
      cases WhRed.of_whnf (head_whnf laws.shape _) red
      exact .inr ⟨notUniverse, rfl⟩
  | pi red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | sigma red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | ident red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | num red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | prop red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | holds red => cases WhRed.of_whnf (head_whnf laws.shape _) red
  | rigid red =>
      exact absurd (WhRed.of_whnf (head_whnf laws.shape _) red) appSpine_const_ne_head

/-- The numbers denote the pairs of terms with one numeral. -/
theorem Den.num_inv {n : Nat} {ξ : World M.reading n} {R : Rel Head n} (den : Den M ξ (.const M.num) R) :
    R = fun t t' => ∃ k, NumVal M.reading t k ∧ NumVal M.reading t' k := by
  obtain ⟨_, interp⟩ := den
  exact InterpAt.deterministic laws interp (Interp.num .refl)

/-- Terms related at an identity type witness that its endpoints are related. -/
theorem Den.id_endpoints {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n} {R : Rel Head n}
    (den : Den M ξ (.id A a b) R) {t u : Tm Head n} (h : R t u) {RA : Rel Head n}
    (denA : Den M ξ A RA) : RA a b := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨RA', rfl, interpA, -, -⟩ := InterpAt.id_inv laws interp
  rw [Den.deterministic laws denA ⟨l, interpA⟩]
  exact h

/-- An identity type between a point and itself relates every pair of terms. -/
theorem Den.id_diag {n : Nat} {ξ : World M.reading n} {A a : Tm Head n} {R : Rel Head n}
    (den : Den M ξ (.id A a a) R) (t u : Tm Head n) : R t u := by
  obtain ⟨_, interp⟩ := den
  obtain ⟨RA, rfl, -, ha, -⟩ := InterpAt.id_inv laws interp
  exact ha

end Inversion

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
