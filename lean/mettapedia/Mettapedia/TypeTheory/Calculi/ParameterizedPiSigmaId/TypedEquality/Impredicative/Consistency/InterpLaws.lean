import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Interp

/-!
# Laws of the interpretation: expansion and determinism

A type has the interpretation of its weak-head reducts, and at most one
interpretation at a level: every clause reads a weak-head normal form of its
own shape.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-- The roles that make the interpreted shapes weak-head normal and distinct. -/
structure Model.Laws (M : Model Head L) : Prop where
  truth : M.toSetting.Laws
  num : M.roles M.num = .inductive [(M.zero, []), (M.suc, [.recursive])]
  prop : M.roles M.prop = .rigid
  holds : M.roles M.holds = .rigid

/-- The laws of the model's reading. -/
theorem Model.Laws.reading {M : Model Head L} (laws : M.Laws) : M.reading.Laws :=
  laws.truth.truthReading

/-! ## Spines of constants -/

theorem appSpine_const_eq_const {n : Nat} {T c : DeclName} {args : List (Tm Head n)}
    (e : appSpine (.const T) args = .const c) : T = c ∧ args = [] := by
  have := appSpine_injective (as := args) (bs := []) (by trivial) (by trivial) e
  exact ⟨Tm.const.inj this.1, this.2⟩

theorem appSpine_const_eq_app {n : Nat} {T c : DeclName} {args : List (Tm Head n)}
    {x : Tm Head n} (e : appSpine (.const T) args = .app (.const c) x) : T = c ∧ args = [x] := by
  have := appSpine_injective (as := args) (bs := [x]) (by trivial) (by trivial) e
  exact ⟨Tm.const.inj this.1, this.2⟩

theorem appSpine_const_ne_head {n : Nat} {T : DeclName} {args : List (Tm Head n)}
    {h : Head} : appSpine (.const T) args ≠ .head h := by
  intro e
  have := appSpine_injective (as := args) (bs := []) (by trivial) (by trivial) e
  cases this.1

theorem appSpine_const_ne_pi {n : Nat} {T : DeclName} {args : List (Tm Head n)}
    {A : Tm Head n} {B : Tm Head (n + 1)} : appSpine (.const T) args ≠ .pi A B := by
  intro e
  have := appSpine_injective (as := args) (bs := []) (by trivial) (by trivial) e
  cases this.1

theorem appSpine_const_ne_sigma {n : Nat} {T : DeclName} {args : List (Tm Head n)}
    {A : Tm Head n} {B : Tm Head (n + 1)} : appSpine (.const T) args ≠ .sigma A B := by
  intro e
  have := appSpine_injective (as := args) (bs := []) (by trivial) (by trivial) e
  cases this.1

theorem appSpine_const_ne_id {n : Nat} {T : DeclName} {args : List (Tm Head n)}
    {A a b : Tm Head n} : appSpine (.const T) args ≠ .id A a b := by
  intro e
  have := appSpine_injective (as := args) (bs := []) (by trivial) (by trivial) e
  cases this.1

/-! ## Weak-head normal forms of the interpreted shapes -/

namespace Model.Laws

variable (laws : M.Laws)
include laws

theorem shape : RootShape M.rules M.roles := laws.reading.shape

theorem whnf_rigidSpine {n : Nat} {T : DeclName} (role : M.roles T = .rigid)
    (args : List (Tm Head n)) : Whnf M.rules M.roles (appSpine (.const T) args) :=
  constSpine_whnf laws.shape (by intro a s h; rw [role] at h; cases h) args

theorem whnf_num {n : Nat} : Whnf M.rules M.roles (.const M.num : Tm Head n) :=
  constSpine_whnf laws.shape (by intro a s h; rw [laws.num] at h; cases h) (n := n) []

theorem whnf_prop {n : Nat} : Whnf M.rules M.roles (.const M.prop : Tm Head n) :=
  laws.whnf_rigidSpine laws.prop (n := n) []

theorem whnf_holds {n : Nat} (c : Tm Head n) :
    Whnf M.rules M.roles (.app (.const M.holds) c) :=
  laws.whnf_rigidSpine laws.holds [c]

theorem num_ne_prop : M.num ≠ M.prop := by
  intro e
  have h := laws.num
  rw [e, laws.prop] at h
  cases h

theorem num_ne_holds : M.num ≠ M.holds := by
  intro e
  have h := laws.num
  rw [e, laws.holds] at h
  cases h

end Model.Laws

/-! ## Expansion -/

variable {l : L} {below : L → IRel M.reading}

theorem Interp.expand {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n}
    (red : WhRed M.rules M.roles A A') (interp : Interp M l below ξ A' R) :
    Interp M l below ξ A R := by
  cases interp with
  | sort isUniverse level r => exact .sort isUniverse level (red.trans r)
  | ground notUniverse r => exact .ground notUniverse (red.trans r)
  | pi r P domInterp codInterp codRespect => exact .pi (red.trans r) P domInterp codInterp codRespect
  | sigma r P domInterp codInterp codRespect =>
      exact .sigma (red.trans r) P domInterp codInterp codRespect
  | ident r R tyInterp lhsRefl rhsRefl => exact .ident (red.trans r) R tyInterp lhsRefl rhsRefl
  | num r => exact .num (red.trans r)
  | prop r => exact .prop (red.trans r)
  | holds r good => exact .holds (red.trans r) good
  | rigid r role notProp notHolds => exact .rigid (red.trans r) role notProp notHolds

/-! ## Determinism -/

theorem PiRel.rel_ext {n : Nat} {ξ : World M.reading n} {P P' : PiRel Head ξ}
    (dom : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ), P.dom w = P'.dom w)
    (cod : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
      (ha : P.dom w a a) (ha' : P'.dom w a a), P.cod w ha = P'.cod w ha') :
    P.rel = P'.rel := by
  funext f g
  apply propext
  constructor
  · intro h m ξ' ρ w a b ha' hab'
    have ha : P.dom w a a := by rw [dom w]; exact ha'
    have hab : P.dom w a b := by rw [dom w]; exact hab'
    rw [← cod w ha ha']
    exact h w ha hab
  · intro h m ξ' ρ w a b ha hab
    have ha' : P'.dom w a a := by rw [← dom w]; exact ha
    have hab' : P'.dom w a b := by rw [← dom w]; exact hab
    rw [cod w ha ha']
    exact h w ha' hab'

theorem PiRel.pairRel_ext {n : Nat} {ξ : World M.reading n} {P P' : PiRel Head ξ}
    (dom : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ), P.dom w = P'.dom w)
    (cod : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
      (ha : P.dom w a a) (ha' : P'.dom w a a), P.cod w ha = P'.cod w ha') :
    P.pairRel = P'.pairRel := by
  funext p q
  apply propext
  constructor
  · rintro ⟨hp, hpq, hc⟩
    have hp' : P'.dom (Morph.id ξ) (.fst p) (.fst p) := by rw [← dom]; exact hp
    refine ⟨hp', by rw [← dom]; exact hpq, ?_⟩
    rw [← cod _ hp hp']
    exact hc
  · rintro ⟨hp', hpq', hc'⟩
    have hp : P.dom (Morph.id ξ) (.fst p) (.fst p) := by rw [dom]; exact hp'
    refine ⟨hp, by rw [dom]; exact hpq', ?_⟩
    rw [cod _ hp hp']
    exact hc'

theorem Interp.deterministic (laws : M.Laws) : ∀ {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {R R' : Rel Head n}, Interp M l below ξ A R → Interp M l below ξ A R' → R = R'
  | _, _, _, _, _, .sort isUniverse _ red, second => by
      cases second with
      | sort _ _ red' =>
          cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _)
            (head_whnf laws.shape _)
          rfl
      | ground notUniverse red' =>
          cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _)
            (head_whnf laws.shape _)
          exact absurd isUniverse notUniverse
      | pi red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (id_whnf laws.shape _ _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) laws.whnf_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (laws.whnf_holds _)
      | rigid red' role =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _)
            (laws.whnf_rigidSpine role _)).symm appSpine_const_ne_head
  | _, _, _, _, _, .ground notUniverse red, second => by
      cases second with
      | sort isUniverse _ red' =>
          cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _)
            (head_whnf laws.shape _)
          exact absurd isUniverse notUniverse
      | ground _ _ => rfl
      | pi red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (id_whnf laws.shape _ _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) laws.whnf_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' (head_whnf laws.shape _) (laws.whnf_holds _)
      | rigid red' role => rfl
  | _, _, _, _, _, .pi red P domInterp codInterp _, second => by
      cases second with
      | pi red' P' domInterp' codInterp' _ =>
          cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _)
            (pi_whnf laws.shape _ _)
          have dom : ∀ {m : Nat} {ξ' : World M.reading m} {ρ} (w : Morph _ ξ' ρ), P.dom w = P'.dom w :=
            fun {_ _ _} w => Interp.deterministic laws (domInterp w) (domInterp' w)
          exact PiRel.rel_ext dom fun {_ _ _} w {_} ha ha' =>
            Interp.deterministic laws (codInterp w ha) (codInterp' w ha')
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) (head_whnf laws.shape _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) (id_whnf laws.shape _ _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) laws.whnf_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _) (laws.whnf_holds _)
      | rigid red' role =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (pi_whnf laws.shape _ _)
            (laws.whnf_rigidSpine role _)).symm appSpine_const_ne_pi
  | _, _, _, _, _, .sigma red P domInterp codInterp _, second => by
      cases second with
      | sigma red' P' domInterp' codInterp' _ =>
          cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _)
            (sigma_whnf laws.shape _ _)
          have dom : ∀ {m : Nat} {ξ' : World M.reading m} {ρ} (w : Morph _ ξ' ρ), P.dom w = P'.dom w :=
            fun {_ _ _} w => Interp.deterministic laws (domInterp w) (domInterp' w)
          exact PiRel.pairRel_ext dom fun {_ _ _} w {_} ha ha' =>
            Interp.deterministic laws (codInterp w ha) (codInterp' w ha')
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) (head_whnf laws.shape _)
      | pi red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) (id_whnf laws.shape _ _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) laws.whnf_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _) (laws.whnf_holds _)
      | rigid red' role =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (sigma_whnf laws.shape _ _)
            (laws.whnf_rigidSpine role _)).symm appSpine_const_ne_sigma
  | _, _, _, _, _, .ident red R tyInterp _ _, second => by
      cases second with
      | ident red' R' tyInterp' _ _ =>
          cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _)
            (id_whnf laws.shape _ _ _)
          rw [Interp.deterministic laws tyInterp tyInterp']
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) (head_whnf laws.shape _)
      | pi red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) (sigma_whnf laws.shape _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) laws.whnf_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _) (laws.whnf_holds _)
      | rigid red' role =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (id_whnf laws.shape _ _ _)
            (laws.whnf_rigidSpine role _)).symm appSpine_const_ne_id
  | _, _, _, _, _, .num red, second => by
      cases second with
      | num _ => rfl
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (head_whnf laws.shape _)
      | pi red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (id_whnf laws.shape _ _ _)
      | prop red' =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_num laws.whnf_prop
          exact absurd (Tm.const.inj e) laws.num_ne_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_num (laws.whnf_holds _)
      | rigid red' role =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_num (laws.whnf_rigidSpine role _)
          obtain ⟨rfl, _⟩ := appSpine_const_eq_const e.symm
          rw [laws.num] at role
          cases role
  | _, _, _, _, _, .prop red, second => by
      cases second with
      | prop _ => rfl
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (head_whnf laws.shape _)
      | pi red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (id_whnf laws.shape _ _ _)
      | num red' =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_prop laws.whnf_num
          exact absurd (Tm.const.inj e).symm laws.num_ne_prop
      | holds red' => cases WhRed.whnf_unique laws.shape red red' laws.whnf_prop (laws.whnf_holds _)
      | rigid red' role notProp =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_prop (laws.whnf_rigidSpine role _)
          exact absurd (appSpine_const_eq_const e.symm).1 notProp
  | _, _, _, _, _, .holds red _, second => by
      cases second with
      | holds red' =>
          cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (laws.whnf_holds _)
          rfl
      | sort _ _ red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (head_whnf laws.shape _)
      | ground _ red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (head_whnf laws.shape _)
      | pi red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (pi_whnf laws.shape _ _)
      | sigma red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (sigma_whnf laws.shape _ _)
      | ident red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) (id_whnf laws.shape _ _ _)
      | num red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) laws.whnf_num
      | prop red' => cases WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _) laws.whnf_prop
      | rigid red' role _ notHolds =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_holds _)
            (laws.whnf_rigidSpine role _)
          exact absurd (appSpine_const_eq_app e.symm).1 notHolds
  | _, _, _, _, _, .rigid red role notProp notHolds, second => by
      cases second with
      | rigid _ _ _ _ => rfl
      | ground _ _ => rfl
      | sort _ _ red' =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _)
            (head_whnf laws.shape _)) appSpine_const_ne_head
      | pi red' =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _)
            (pi_whnf laws.shape _ _)) appSpine_const_ne_pi
      | sigma red' =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _)
            (sigma_whnf laws.shape _ _)) appSpine_const_ne_sigma
      | ident red' =>
          exact absurd (WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _)
            (id_whnf laws.shape _ _ _)) appSpine_const_ne_id
      | num red' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _) laws.whnf_num
          obtain ⟨rfl, _⟩ := appSpine_const_eq_const e
          rw [laws.num] at role
          cases role
      | prop red' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _) laws.whnf_prop
          exact absurd (appSpine_const_eq_const e).1 notProp
      | holds red' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_rigidSpine role _)
            (laws.whnf_holds _)
          exact absurd (appSpine_const_eq_app e).1 notHolds

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
