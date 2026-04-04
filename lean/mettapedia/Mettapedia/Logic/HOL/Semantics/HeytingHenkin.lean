import Mathlib.Order.CompleteBooleanAlgebra
import Foundation.Logic.Semantics
import Mettapedia.Logic.HOL.Syntax.Closed

namespace Mettapedia.Logic.HOL

open LO
open Order

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Ty

/-- The ambient carrier associated to a simple HOL type over a truth object `Ω`. -/
def denoteHeyting
    (Carrier : Base → Type (max (u + 1) w)) (Ω : Type (max (u + 1) w)) :
    Ty Base → Type (max (u + 1) w)
  | .prop => Ω
  | .base b => Carrier b
  | .arr σ τ => denoteHeyting Carrier Ω σ → denoteHeyting Carrier Ω τ

end Ty

/--
A raw intuitionistic/extensional Henkin-style premodel:
- ambient carriers for base types,
- an `Order.Frame` truth object `Ω`,
- admissible quantifier domains at each type, including `prop`,
- and an explicit `Ω`-valued equality on base types.
-/
structure HeytingPreModel (Base : Type u) (Const : Ty Base → Type v) where
  Ω : Type (max (u + 1) w)
  instFrame : Order.Frame Ω
  Carrier : Base → Type (max (u + 1) w)
  adm : (τ : Ty Base) → Ty.denoteHeyting Carrier Ω τ → Prop
  base_mem : ∀ b (x : Carrier b), adm (.base b) x
  app_mem :
    ∀ {σ τ} {f : Ty.denoteHeyting Carrier Ω (σ ⇒ τ)} {x : Ty.denoteHeyting Carrier Ω σ},
      adm (σ ⇒ τ) f → adm σ x → adm τ (f x)
  constDen : {τ : Ty Base} → Const τ → Ty.denoteHeyting Carrier Ω τ
  const_mem : ∀ {τ : Ty Base} (c : Const τ), adm τ (constDen c)
  baseEq : (b : Base) → Carrier b → Carrier b → Ω
  baseEq_refl : ∀ b (x : Carrier b), baseEq b x x = ⊤
  baseEq_symm : ∀ b (x y : Carrier b), baseEq b x y ≤ baseEq b y x
  baseEq_trans :
    ∀ b (x y z : Carrier b), baseEq b x y ⊓ baseEq b y z ≤ baseEq b x z

attribute [instance] HeytingPreModel.instFrame

namespace HeytingPreModel

abbrev Valuation (M : HeytingPreModel Base Const) (Γ : Ctx Base) :=
  ∀ {τ}, Var Γ τ → Ty.denoteHeyting M.Carrier M.Ω τ

def ValuationAdmissible (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) : Prop :=
  ∀ {τ} (v : Var Γ τ), M.adm τ (ρ v)

def extend (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (x : Ty.denoteHeyting M.Carrier M.Ω σ) :
    Valuation M (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

theorem extend_admissible (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    {ρ : Valuation M Γ} {x : Ty.denoteHeyting M.Carrier M.Ω σ}
    (hρ : ValuationAdmissible M ρ) (hx : M.adm σ x) :
    ValuationAdmissible M (extend M ρ x) := by
  intro τ v
  cases v with
  | vz =>
      simpa using hx
  | vs v =>
      exact hρ v

/-- Infimum over the admissible elements of a type. Empty domains give `⊤`. -/
def allAdmissible (M : HeytingPreModel Base Const) {σ : Ty Base}
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) : M.Ω :=
  sInf (Set.range p)

/-- Supremum over the admissible elements of a type. Empty domains give `⊥`. -/
def anyAdmissible (M : HeytingPreModel Base Const) {σ : Ty Base}
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) : M.Ω :=
  sSup (Set.range p)

/-- Availability-weighted universal quantification over admissible elements.

This is the honest growing-domain variant: each admissible element `x` carries
an `Ω`-valued availability guard, so worlds where `x` is unavailable only
require the implication premise vacuously.
-/
def allAvailable (M : HeytingPreModel Base Const) {σ : Ty Base}
    (avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω)
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) : M.Ω :=
  sInf (Set.range (fun x => avail x ⇨ p x))

/-- Availability-weighted existential quantification over admissible elements.

This is the honest growing-domain variant: a witness contributes only where it
is available.
-/
def anyAvailable (M : HeytingPreModel Base Const) {σ : Ty Base}
    (avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω)
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) : M.Ω :=
  sSup (Set.range (fun x => avail x ⊓ p x))

@[simp] theorem allAvailable_top (M : HeytingPreModel Base Const) {σ : Ty Base}
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) :
    allAvailable M (σ := σ) (fun _ => (⊤ : M.Ω)) p = allAdmissible M p := by
  simp [allAvailable, allAdmissible]

@[simp] theorem anyAvailable_top (M : HeytingPreModel Base Const) {σ : Ty Base}
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) :
    anyAvailable M (σ := σ) (fun _ => (⊤ : M.Ω)) p = anyAdmissible M p := by
  simp [anyAvailable, anyAdmissible]

/-- Legacy universal quantification is below availability-weighted universal
quantification.

Positive example:
adding availability guards weakens the universal requirement at worlds where an
element is unavailable.

Negative example:
this does not prove any converse inequality in general.
-/
theorem allAdmissible_le_allAvailable
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    (avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω)
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) :
    allAdmissible M p ≤ allAvailable M (σ := σ) avail p := by
  unfold allAdmissible allAvailable
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  refine (le_himp_iff).2 ?_
  exact inf_le_left.trans (sInf_le (by exact ⟨x, rfl⟩))

theorem le_allAvailable (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (h : ∀ x, a ⊓ avail x ≤ p x) :
    a ≤ allAvailable M (σ := σ) avail p := by
  unfold allAvailable
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  exact (le_himp_iff).2 (h x)

theorem allAvailable_le (M : HeytingPreModel Base Const) {σ : Ty Base}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x}) :
    allAvailable M (σ := σ) avail p ≤ avail x ⇨ p x :=
  sInf_le (by exact ⟨x, rfl⟩)

/-- Elimination shape for availability-weighted universals.

Positive example:
from `c ≤ ∀[avail] x, p x`, we can always conclude `c ⊓ avail x ≤ p x`.

Negative example:
without a separate proof that `c ≤ avail x`, this does not imply `c ≤ p x`.
-/
theorem allAvailable_elim
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (hAll : a ≤ allAvailable M (σ := σ) avail p)
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x}) :
    a ⊓ avail x ≤ p x := by
  exact (le_himp_iff).1 (le_trans hAll (allAvailable_le M (x := x)))

/-- Availability-weighted universal elimination with an explicit availability
premise for the witness.

Positive example:
if `c ≤ avail x`, then the guard from `allAvailable_elim` disappears.

Negative example:
without `c ≤ avail x`, this specialization is invalid in general.
-/
theorem allAvailable_elim_of_available
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (hAll : a ≤ allAvailable M (σ := σ) avail p)
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x})
    (hAvail : a ≤ avail x) :
    a ≤ p x := by
  exact le_trans (le_inf le_rfl hAvail) (allAvailable_elim M hAll x)

/-- Availability-weighted existential quantification is below legacy existential
quantification.

Positive example:
availability can only remove witness contributions, never add new ones.

Negative example:
this does not prove equality unless availability is `⊤`.
-/
theorem anyAvailable_le_anyAdmissible
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    (avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω)
    (p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) :
    anyAvailable M (σ := σ) avail p ≤ anyAdmissible M p := by
  unfold anyAvailable anyAdmissible
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  exact inf_le_right.trans (le_sSup (by exact ⟨x, rfl⟩))

theorem anyAvailable_le (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (h : ∀ x, avail x ⊓ p x ≤ a) :
    anyAvailable M (σ := σ) avail p ≤ a := by
  unfold anyAvailable
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  exact h x

theorem le_anyAvailable (M : HeytingPreModel Base Const) {σ : Ty Base}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x}) :
    avail x ⊓ p x ≤ anyAvailable M (σ := σ) avail p :=
  le_sSup (by exact ⟨x, rfl⟩)

/-- Availability-weighted existential introduction from an explicit witness.

Positive example:
if `c` proves both witness availability and body truth, then `c` proves the
existential.

Negative example:
without availability, body truth alone is not enough for `anyAvailable`.
-/
theorem le_anyAvailable_of_available
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x})
    (hAvail : a ≤ avail x)
    (hBody : a ≤ p x) :
    a ≤ anyAvailable M (σ := σ) avail p := by
  exact le_trans (le_inf hAvail hBody) (le_anyAvailable M (x := x))

/-- Pathological boundary check: if everything is unavailable, availability-
weighted universal quantification collapses to `⊤`. -/
theorem allAvailable_eq_top_of_forall_bot
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (hbot : ∀ x, avail x = (⊥ : M.Ω)) :
    allAvailable M (σ := σ) avail p = (⊤ : M.Ω) := by
  apply le_antisymm le_top
  refine le_allAvailable M (a := (⊤ : M.Ω)) ?_
  intro x
  simp [hbot x]

/-- Pathological boundary check: if everything is unavailable, availability-
weighted existential quantification collapses to `⊥`. -/
theorem anyAvailable_eq_bot_of_forall_bot
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    {avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (hbot : ∀ x, avail x = (⊥ : M.Ω)) :
    anyAvailable M (σ := σ) avail p = (⊥ : M.Ω) := by
  apply le_antisymm
  · refine anyAvailable_le M (a := (⊥ : M.Ω)) ?_
    intro x
    simp [hbot x]
  · exact bot_le

theorem le_allAdmissible (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω} {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (h : ∀ x, a ≤ p x) :
    a ≤ allAdmissible M p := by
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  exact h x

theorem allAdmissible_le (M : HeytingPreModel Base Const) {σ : Ty Base}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x}) :
    allAdmissible M p ≤ p x :=
  sInf_le (by exact ⟨x, rfl⟩)

theorem anyAdmissible_le (M : HeytingPreModel Base Const) {σ : Ty Base}
    {a : M.Ω} {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (h : ∀ x, p x ≤ a) :
    anyAdmissible M p ≤ a := by
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  exact h x

theorem le_anyAdmissible (M : HeytingPreModel Base Const) {σ : Ty Base}
    {p : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω}
    (x : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x}) :
    p x ≤ anyAdmissible M p :=
  le_sSup (by exact ⟨x, rfl⟩)

/-- `Ω`-valued extensional typed equality. -/
def Eqv (M : HeytingPreModel Base Const) :
    (τ : Ty Base) →
      Ty.denoteHeyting M.Carrier M.Ω τ →
      Ty.denoteHeyting M.Carrier M.Ω τ →
      M.Ω
  | .prop, p, q => (p ⇨ q) ⊓ (q ⇨ p)
  | .base b, x, y => M.baseEq b x y
  | .arr σ τ, f, g =>
      allAdmissible M (σ := σ) (fun x => Eqv M τ (f x.1) (g x.1))

@[simp] theorem eqv_prop (M : HeytingPreModel Base Const)
    {p q : M.Ω} :
    Eqv M .prop p q = (p ⇨ q) ⊓ (q ⇨ p) := rfl

@[simp] theorem eqv_base (M : HeytingPreModel Base Const) {b : Base}
    {x y : M.Carrier b} :
    Eqv M (.base b) x y = M.baseEq b x y := rfl

@[simp] theorem eqv_arr (M : HeytingPreModel Base Const) {σ τ : Ty Base}
    {f g : Ty.denoteHeyting M.Carrier M.Ω (σ ⇒ τ)} :
    Eqv M (σ ⇒ τ) f g =
      allAdmissible M (σ := σ) (fun x => Eqv M τ (f x.1) (g x.1)) := rfl

theorem eqv_refl (M : HeytingPreModel Base Const) :
    ∀ {τ : Ty Base} {x : Ty.denoteHeyting M.Carrier M.Ω τ},
      M.adm τ x → Eqv M τ x x = ⊤
  | .prop, p, hp => by
      simp [Eqv]
  | .base b, x, hx => M.baseEq_refl b x
  | .arr σ τ, f, hf => by
      apply le_antisymm le_top
      refine le_allAdmissible M ?_
      intro x
      exact (eqv_refl M (τ := τ) (x := f x.1) (M.app_mem hf x.2)).ge

/-- Reflexive equality under availability-weighted existential quantification
reduces to the supremum of availability.

Positive example:
when `avail` encodes worldwise support of a local witness section, this theorem
states that `∃ x, x = x` denotes exactly the union of those supports.

Negative example:
if one keeps the old unweighted `anyAdmissible`, the same formula collapses to
`⊤` as soon as any admissible element exists globally.
-/
theorem anyAvailable_eqv_refl_eq_sSup_avail
    (M : HeytingPreModel Base Const) {σ : Ty Base}
    (avail : {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} → M.Ω) :
    anyAvailable M (σ := σ) avail (fun x => Eqv M σ x.1 x.1) =
      sSup (Set.range avail) := by
  have hfun :
      (fun x =>
          avail x ⊓ Eqv M σ x.1 x.1) = avail := by
    funext x
    have hrefl : Eqv M σ x.1 x.1 = (⊤ : M.Ω) :=
      eqv_refl M (τ := σ) (x := x.1) x.2
    simp [hrefl]
  simp [anyAvailable, hfun]

theorem eqv_symm (M : HeytingPreModel Base Const) :
    ∀ {τ : Ty Base} {x y : Ty.denoteHeyting M.Carrier M.Ω τ},
      Eqv M τ x y ≤ Eqv M τ y x
  | .prop, p, q => by
      rw [eqv_prop, eqv_prop, inf_comm]
  | .base b, x, y => M.baseEq_symm b x y
  | .arr σ τ, f, g => by
      refine le_allAdmissible M ?_
      intro x
      exact (allAdmissible_le M x).trans (eqv_symm M (τ := τ))

theorem eqv_trans (M : HeytingPreModel Base Const) :
    ∀ {τ : Ty Base}
      {x y z : Ty.denoteHeyting M.Carrier M.Ω τ},
      Eqv M τ x y ⊓ Eqv M τ y z ≤ Eqv M τ x z
  | .prop, p, q, r => by
      let p' : M.Ω := p
      let q' : M.Ω := q
      let r' : M.Ω := r
      let e₁ : M.Ω := Eqv M .prop p' q'
      let e₂ : M.Ω := Eqv M .prop q' r'
      change (e₁ ⊓ e₂) ≤ ((p' ⇨ r') ⊓ (r' ⇨ p'))
      apply le_inf
      · exact (le_himp_iff).2 <| by
          have hpq : e₁ ⊓ p' ≤ q' := by
            dsimp [e₁, Eqv]
            calc
              ((p' ⇨ q') ⊓ (q' ⇨ p')) ⊓ p' ≤ (p' ⇨ q') ⊓ p' := by
                exact inf_le_inf_right _ inf_le_left
              _ ≤ q' := by
                rw [inf_comm]
                exact (inf_himp_le : p' ⊓ (p' ⇨ q') ≤ q')
          have hqr : e₂ ⊓ q' ≤ r' := by
            dsimp [e₂, Eqv]
            calc
              ((q' ⇨ r') ⊓ (r' ⇨ q')) ⊓ q' ≤ (q' ⇨ r') ⊓ q' := by
                exact inf_le_inf_right _ inf_le_left
              _ ≤ r' := by
                rw [inf_comm]
                exact (inf_himp_le : q' ⊓ (q' ⇨ r') ≤ r')
          calc
            (e₁ ⊓ e₂) ⊓ p' ≤ e₂ ⊓ q' := by
              simpa [inf_assoc, inf_left_comm, inf_comm] using
                (inf_le_inf_left e₂ hpq)
            _ ≤ r' := hqr
      · exact (le_himp_iff).2 <| by
          have hrq : e₂ ⊓ r' ≤ q' := by
            dsimp [e₂, Eqv]
            calc
              ((q' ⇨ r') ⊓ (r' ⇨ q')) ⊓ r' ≤ (r' ⇨ q') ⊓ r' := by
                exact inf_le_inf_right _ inf_le_right
              _ ≤ q' := by
                rw [inf_comm]
                exact (inf_himp_le : r' ⊓ (r' ⇨ q') ≤ q')
          have hqp : e₁ ⊓ q' ≤ p' := by
            dsimp [e₁, Eqv]
            calc
              ((p' ⇨ q') ⊓ (q' ⇨ p')) ⊓ q' ≤ (q' ⇨ p') ⊓ q' := by
                exact inf_le_inf_right _ inf_le_right
              _ ≤ p' := by
                rw [inf_comm]
                exact (inf_himp_le : q' ⊓ (q' ⇨ p') ≤ p')
          calc
            (e₁ ⊓ e₂) ⊓ r' ≤ e₁ ⊓ q' := by
              simpa [inf_assoc, inf_left_comm, inf_comm] using
                (inf_le_inf_left e₁ hrq)
            _ ≤ p' := hqp
  | .base b, x, y, z => M.baseEq_trans b x y z
  | .arr σ τ, f, g, h => by
      refine le_allAdmissible M ?_
      intro x
      have hxy : Eqv M (σ ⇒ τ) f g ≤ Eqv M τ (f x.1) (g x.1) :=
        allAdmissible_le M x
      have hyz : Eqv M (σ ⇒ τ) g h ≤ Eqv M τ (g x.1) (h x.1) :=
        allAdmissible_le M x
      exact
        calc
          Eqv M (σ ⇒ τ) f g ⊓ Eqv M (σ ⇒ τ) g h
              ≤ Eqv M τ (f x.1) (g x.1) ⊓ Eqv M τ (g x.1) (h x.1) := by
                exact inf_le_inf hxy hyz
          _ ≤ Eqv M τ (f x.1) (h x.1) := eqv_trans M

/-- Availability assignment for quantifier domains at each type.

Positive example:
in growing-domain semantics, this can encode worldwise support of a local
witness section.

Negative example:
using only `⊤` availability recovers fixed-domain quantification and cannot
express local birth of individuals.
-/
abbrev QuantifierAvailability (M : HeytingPreModel Base Const) :=
  (σ : Ty Base) →
    {x : Ty.denoteHeyting M.Carrier M.Ω σ // M.adm σ x} →
      M.Ω

/-- Trivial availability assignment: every admissible element is available
everywhere. -/
abbrev topAvailability (M : HeytingPreModel Base Const) :
    QuantifierAvailability M :=
  fun _ _ => ⊤

/-- Denotation with explicit availability-weighted quantifier semantics.

Positive example:
`all`/`ex` clauses can use world-sensitive availability guards.

Negative example:
this does not replace the legacy denotation; it is an additive bridge layer for
the growing-domain route.
-/
def denoteWithAvailability (M : HeytingPreModel Base Const)
    (avail : QuantifierAvailability M) :
    {Γ : Ctx Base} → {τ : Ty Base} →
      Term Const Γ τ → Valuation M Γ → Ty.denoteHeyting M.Carrier M.Ω τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => M.constDen c
  | _, _, .app f t, ρ => (denoteWithAvailability M avail f ρ) (denoteWithAvailability M avail t ρ)
  | _, _, .lam t, ρ => fun x => denoteWithAvailability M avail t (extend M ρ x)
  | _, .prop, .top, _ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from (⊤ : M.Ω)
  | _, .prop, .bot, _ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from (⊥ : M.Ω)
  | _, .prop, .and φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denoteWithAvailability M avail (τ := .prop) φ ρ) ⊓
          (show M.Ω from denoteWithAvailability M avail (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .or φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denoteWithAvailability M avail (τ := .prop) φ ρ) ⊔
          (show M.Ω from denoteWithAvailability M avail (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .imp φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denoteWithAvailability M avail (τ := .prop) φ ρ) ⇨
          (show M.Ω from denoteWithAvailability M avail (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .not φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (((show M.Ω from denoteWithAvailability M avail (τ := .prop) φ ρ) ⇨ (⊥ : M.Ω)) : M.Ω)
  | _, .prop, .eq t u, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from Eqv M _ (denoteWithAvailability M avail t ρ) (denoteWithAvailability M avail u ρ)) : M.Ω)
  | _, .prop, .all (σ := σ) φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (allAvailable M (σ := σ) (avail σ) (fun x =>
          (show M.Ω from denoteWithAvailability M avail (τ := .prop) φ (extend M ρ x.1))) : M.Ω)
  | _, .prop, .ex (σ := σ) φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (anyAvailable M (σ := σ) (avail σ) (fun x =>
          (show M.Ω from denoteWithAvailability M avail (τ := .prop) φ (extend M ρ x.1))) : M.Ω)

/-- Denotation with availability, specialized to proposition-valued terms. -/
abbrev denoteFormulaWithAvailability (M : HeytingPreModel Base Const)
    (avail : QuantifierAvailability M) {Γ : Ctx Base}
    (φ : Formula Const Γ) (ρ : Valuation M Γ) : M.Ω :=
  show M.Ω from denoteWithAvailability M avail (τ := .prop) φ ρ

/-- Context denotation under availability-weighted quantifier semantics. -/
def contextDenoteWithAvailability (M : HeytingPreModel Base Const)
    (avail : QuantifierAvailability M) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) : M.Ω :=
  Δ.foldr (fun φ acc => denoteFormulaWithAvailability M avail φ ρ ⊓ acc) ⊤

/-- `modelsFrom` under availability-weighted quantifier semantics. -/
def modelsFromWithAvailability (M : HeytingPreModel Base Const)
    (avail : QuantifierAvailability M) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) : Prop :=
  contextDenoteWithAvailability M avail Δ ρ ≤
    denoteFormulaWithAvailability M avail φ ρ

/-- Denotation of HOL terms in an intuitionistic/extensional premodel. -/
def denote (M : HeytingPreModel Base Const) :
    {Γ : Ctx Base} → {τ : Ty Base} →
      Term Const Γ τ → Valuation M Γ → Ty.denoteHeyting M.Carrier M.Ω τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => M.constDen c
  | _, _, .app f t, ρ => (denote M f ρ) (denote M t ρ)
  | _, _, .lam t, ρ => fun x => denote M t (extend M ρ x)
  | _, .prop, .top, _ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from (⊤ : M.Ω)
  | _, .prop, .bot, _ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from (⊥ : M.Ω)
  | _, .prop, .and φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denote M (τ := .prop) φ ρ) ⊓
          (show M.Ω from denote M (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .or φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denote M (τ := .prop) φ ρ) ⊔
          (show M.Ω from denote M (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .imp φ ψ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from denote M (τ := .prop) φ ρ) ⇨
          (show M.Ω from denote M (τ := .prop) ψ ρ) : M.Ω)
  | _, .prop, .not φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (((show M.Ω from denote M (τ := .prop) φ ρ) ⇨ (⊥ : M.Ω)) : M.Ω)
  | _, .prop, .eq t u, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        ((show M.Ω from Eqv M _ (denote M t ρ) (denote M u ρ)) : M.Ω)
  | _, .prop, .all φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (allAdmissible M (fun x =>
          (show M.Ω from denote M (τ := .prop) φ (extend M ρ x.1))) : M.Ω)
  | _, .prop, .ex φ, ρ =>
      show Ty.denoteHeyting M.Carrier M.Ω .prop from
        (anyAdmissible M (fun x =>
          (show M.Ω from denote M (τ := .prop) φ (extend M ρ x.1))) : M.Ω)

/-- Legacy denotation is the `topAvailability` specialization. -/
theorem denoteWithAvailability_top_eq_denote
    (M : HeytingPreModel Base Const) :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term Const Γ τ) (ρ : Valuation M Γ),
        denoteWithAvailability M (topAvailability M) t ρ = denote M t ρ
  | _, _, .var v, ρ => rfl
  | _, _, .const c, ρ => rfl
  | _, _, .app f t, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, _, .lam t, ρ => by
      funext x
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .top, ρ => rfl
  | _, .prop, .bot, ρ => rfl
  | _, .prop, .and φ ψ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .or φ ψ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .imp φ ψ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .not φ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .eq t u, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .all (σ := σ) φ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]
  | _, .prop, .ex (σ := σ) φ, ρ => by
      simp [denoteWithAvailability, denote, denoteWithAvailability_top_eq_denote, *]

/-- Denotation specialized to proposition-valued terms. -/
abbrev denoteFormula (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (φ : Formula Const Γ) (ρ : Valuation M Γ) : M.Ω :=
  show M.Ω from denote M (τ := .prop) φ ρ

def contextDenote (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) : M.Ω :=
  Δ.foldr (fun φ acc => denoteFormula M φ ρ ⊓ acc) ⊤

def modelsFrom (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) : Prop :=
  contextDenote M Δ ρ ≤ denoteFormula M φ ρ

def models (M : HeytingPreModel Base Const) (φ : ClosedFormula Const) : Prop :=
  denoteFormula M φ (fun v => nomatch v) = ⊤

@[simp] theorem contextDenote_nil (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) :
    contextDenote M [] ρ = ⊤ := rfl

@[simp] theorem contextDenote_cons (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (φ : Formula Const Γ) (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) :
    contextDenote M (φ :: Δ) ρ = denoteFormula M φ ρ ⊓ contextDenote M Δ ρ := rfl

@[simp] theorem denoteFormulaWithAvailability_top_eq_denoteFormula
    (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (φ : Formula Const Γ) (ρ : Valuation M Γ) :
    denoteFormulaWithAvailability M (topAvailability M) φ ρ =
      denoteFormula M φ ρ := by
  simpa [denoteFormulaWithAvailability, denoteFormula] using
    (denoteWithAvailability_top_eq_denote M (t := φ) (ρ := ρ))

@[simp] theorem contextDenoteWithAvailability_nil
    (M : HeytingPreModel Base Const) (avail : QuantifierAvailability M)
    {Γ : Ctx Base} (ρ : Valuation M Γ) :
    contextDenoteWithAvailability M avail [] ρ = ⊤ :=
  rfl

@[simp] theorem contextDenoteWithAvailability_cons
    (M : HeytingPreModel Base Const) (avail : QuantifierAvailability M)
    {Γ : Ctx Base} (φ : Formula Const Γ) (Δ : List (Formula Const Γ))
    (ρ : Valuation M Γ) :
    contextDenoteWithAvailability M avail (φ :: Δ) ρ =
      denoteFormulaWithAvailability M avail φ ρ ⊓
        contextDenoteWithAvailability M avail Δ ρ :=
  rfl

theorem contextDenoteWithAvailability_top_eq_contextDenote
    (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) :
    contextDenoteWithAvailability M (topAvailability M) Δ ρ =
      contextDenote M Δ ρ := by
  induction Δ with
  | nil =>
      simp [contextDenoteWithAvailability, contextDenote]
  | cons φ Δ ih =>
      simp [contextDenoteWithAvailability, contextDenote]

theorem modelsFromWithAvailability_top_iff_modelsFrom
    (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) :
    modelsFromWithAvailability M (topAvailability M) Δ φ ρ ↔
      modelsFrom M Δ φ ρ := by
  constructor <;> intro h <;>
    simpa [modelsFromWithAvailability, modelsFrom,
      contextDenoteWithAvailability_top_eq_contextDenote] using h

theorem contextDenote_le_of_mem (M : HeytingPreModel Base Const) {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (ρ : Valuation M Γ)
    (hφ : φ ∈ Δ) :
    contextDenote M Δ ρ ≤ denoteFormula M φ ρ := by
  induction Δ with
  | nil =>
      cases hφ
  | cons ψ Δ ih =>
      rw [contextDenote_cons]
      rw [List.mem_cons] at hφ
      rcases hφ with hφ | hφ
      · subst hφ
        exact inf_le_left
      · exact le_trans inf_le_right (ih hφ)

end HeytingPreModel

/--
A Heyting-Henkin model is a premodel where term denotations are admissible and
admissible functions respect the typed equality relation of their argument type.
-/
structure HeytingHenkinModel (Base : Type u) (Const : Ty Base → Type v)
    extends HeytingPreModel Base Const where
  term_closed :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term Const Γ τ) (ρ : HeytingPreModel.Valuation toHeytingPreModel Γ),
      HeytingPreModel.ValuationAdmissible toHeytingPreModel ρ →
        toHeytingPreModel.adm τ (HeytingPreModel.denote toHeytingPreModel t ρ)
  app_respects_eq :
    ∀ {σ τ} {f : Ty.denoteHeyting Carrier Ω (σ ⇒ τ)},
      adm (σ ⇒ τ) f →
      ∀ {x y : Ty.denoteHeyting Carrier Ω σ},
        adm σ x → adm σ y →
        HeytingPreModel.Eqv toHeytingPreModel σ x y ≤
          HeytingPreModel.Eqv toHeytingPreModel τ (f x) (f y)

namespace HeytingHenkinModel

instance (M : HeytingHenkinModel Base Const) : Order.Frame M.Ω :=
  M.toHeytingPreModel.instFrame

abbrev Valuation (M : HeytingHenkinModel Base Const) (Γ : Ctx Base) :=
  HeytingPreModel.Valuation M.toHeytingPreModel Γ

abbrev ValuationAdmissible (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) : Prop :=
  HeytingPreModel.ValuationAdmissible M.toHeytingPreModel ρ

abbrev extend (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (x : Ty.denoteHeyting M.Carrier M.Ω σ) : Valuation M (σ :: Γ) :=
  HeytingPreModel.extend M.toHeytingPreModel ρ x

abbrev Eqv (M : HeytingHenkinModel Base Const) := HeytingPreModel.Eqv M.toHeytingPreModel

abbrev denote (M : HeytingHenkinModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) (ρ : Valuation M Γ) : Ty.denoteHeyting M.Carrier M.Ω τ :=
  HeytingPreModel.denote M.toHeytingPreModel t ρ

/-- Availability assignments that respect the term-construction discipline of
the model: constants are available everywhere, and application preserves
availability. -/
structure AdmissibleAvailability
    (M : HeytingHenkinModel Base Const)
    (avail : HeytingPreModel.QuantifierAvailability M.toHeytingPreModel) : Prop where
  const_available :
    ∀ {τ : Ty Base} (c : Const τ),
      avail τ ⟨M.constDen c, M.const_mem c⟩ = (⊤ : M.Ω)
  app_available :
    ∀ {σ τ : Ty Base}
      {f : Ty.denoteHeyting M.Carrier M.Ω (σ ⇒ τ)}
      {x : Ty.denoteHeyting M.Carrier M.Ω σ}
      (hf : M.adm (σ ⇒ τ) f) (hx : M.adm σ x),
        avail (σ ⇒ τ) ⟨f, hf⟩ ⊓ avail σ ⟨x, hx⟩ ≤
          avail τ ⟨f x, M.app_mem hf hx⟩

/-- The trivial `topAvailability` assignment is always admissible. -/
theorem topAvailability_admissible (M : HeytingHenkinModel Base Const) :
    AdmissibleAvailability M
      (HeytingPreModel.topAvailability M.toHeytingPreModel) := by
  refine ⟨?_, ?_⟩
  · intro τ c
    rfl
  · intro σ τ f x hf hx
    simp [HeytingPreModel.topAvailability]

abbrev contextDenote (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) : M.Ω :=
  HeytingPreModel.contextDenote M.toHeytingPreModel Δ ρ

abbrev modelsFrom (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) : Prop :=
  HeytingPreModel.modelsFrom M.toHeytingPreModel Δ φ ρ

abbrev models (M : HeytingHenkinModel Base Const) (φ : ClosedFormula Const) : Prop :=
  HeytingPreModel.models M.toHeytingPreModel φ

theorem extend_admissible (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    {ρ : Valuation M Γ} {x : Ty.denoteHeyting M.Carrier M.Ω σ}
    (hρ : ValuationAdmissible M ρ) (hx : M.adm σ x) :
    ValuationAdmissible M (extend M ρ x) :=
  HeytingPreModel.extend_admissible M.toHeytingPreModel hρ hx

theorem denote_admissible (M : HeytingHenkinModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    {ρ : Valuation M Γ} (hρ : ValuationAdmissible M ρ) (t : Term Const Γ τ) :
    M.adm τ (denote M t ρ) :=
  M.term_closed t ρ hρ

theorem eqv_refl (M : HeytingHenkinModel Base Const) {τ : Ty Base}
    {x : Ty.denoteHeyting M.Carrier M.Ω τ} (hx : M.adm τ x) :
    Eqv M τ x x = ⊤ :=
  HeytingPreModel.eqv_refl M.toHeytingPreModel hx

theorem eqv_symm (M : HeytingHenkinModel Base Const) {τ : Ty Base}
    {x y : Ty.denoteHeyting M.Carrier M.Ω τ} :
    Eqv M τ x y ≤ Eqv M τ y x :=
  HeytingPreModel.eqv_symm M.toHeytingPreModel

theorem eqv_trans (M : HeytingHenkinModel Base Const) {τ : Ty Base}
    {x y z : Ty.denoteHeyting M.Carrier M.Ω τ} :
    Eqv M τ x y ⊓ Eqv M τ y z ≤ Eqv M τ x z :=
  HeytingPreModel.eqv_trans M.toHeytingPreModel

theorem contextDenote_le_of_mem (M : HeytingHenkinModel Base Const) {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (ρ : Valuation M Γ) (hφ : φ ∈ Δ) :
    contextDenote M Δ ρ ≤ denote M φ ρ :=
  HeytingPreModel.contextDenote_le_of_mem M.toHeytingPreModel ρ hφ

instance : LO.Semantics (HeytingHenkinModel Base Const) (ClosedFormula Const) where
  Models M φ := models M φ

end HeytingHenkinModel

end Mettapedia.Logic.HOL
