import Mettapedia.Logic.HOL.CanonicalModel
import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.HenkinizationInfinity
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-!
# Represented Canonical Values  [AUXILIARY]

This file begins the direct Henkin-style bridge from the cumulative canonical
semantics to the standard `HeytingHenkinModel` interface. It is part of the
HInf/Route 2 infrastructure for witnessed-source signatures, not the mainline
plain completeness route. See `ParamWorld.lean` for the mainline.

The core idea is simple:

- semantic values live over canonical worlds that already contain the cumulative
  Henkin axiom family,
- but admissible values are only those that are represented by closed
  cumulative-Henkin terms,
- and function values are tracked extensionally on represented inputs.

This is the first reusable layer of that bridge; it does not yet package the
full `HeytingHenkinModel`.
-/

/-- Canonical worlds restricted to those containing the cumulative Henkin axioms. -/
abbrev HenkinWorld (Base : Type u) (Const : Ty Base → Type v) :=
  {W : World Base Const // HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier}

instance instLEHenkinWorld :
    LE (HenkinWorld Base Const) where
  le W V := W.1 ≤ V.1

/-- Canonical proposition values over Henkin worlds only. -/
abbrev HenkinTruthVal (Base : Type u) (Const : Ty Base → Type v) :=
  UpperSet (HenkinWorld Base Const)

/-- Canonical truth set restricted to Henkin worlds. -/
def henkinTruthSet
    (φ : ClosedFormula (HInf Base Const)) :
    HenkinTruthVal Base Const where
  carrier := {W | φ ∈ W.1.carrier}
  upper' := by
    intro W V hWV hφ
    exact hWV hφ

@[simp] theorem mem_henkinTruthSet_iff
    {W : HenkinWorld Base Const}
    {φ : ClosedFormula (HInf Base Const)} :
    W ∈ henkinTruthSet (Base := Base) (Const := Const) φ ↔ φ ∈ W.1.carrier :=
  Iff.rfl

/-- Provability from the cumulative Henkin axiom family. -/
def HenkinProvable
    (φ : ClosedFormula (HInf Base Const)) : Prop :=
  ClosedTheorySet.Provable
    (Const := HInf Base Const)
    (HenkinAxioms (Base := Base) (Const := Const))
    φ

/-- Any closed theorem is in particular provable from the Henkin axioms. -/
theorem henkinProvable_of_theorem
    {φ : ClosedFormula (HInf Base Const)}
    (h : ExtDerivation.Theorem (HInf Base Const) φ) :
    HenkinProvable (Base := Base) (Const := Const) φ := by
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := HInf Base Const)
      (T := HenkinAxioms (Base := Base) (Const := Const))
      (Δ := [])
      (by
        intro ψ hψ
        cases hψ)
      h

theorem henkinProvable_eq_symm
    {τ : Ty Base}
    {t u : ClosedTerm (HInf Base Const) τ}
    (htu : HenkinProvable (Base := Base) (Const := Const) (.eq t u)) :
    HenkinProvable (Base := Base) (Const := Const) (.eq u t) := by
  rcases htu with ⟨Γ, hΓ, hDeriv⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqSymm hDeriv⟩

theorem henkinProvable_eq_trans
    {τ : Ty Base}
    {t u v : ClosedTerm (HInf Base Const) τ}
    (htu : HenkinProvable (Base := Base) (Const := Const) (.eq t u))
    (huv : HenkinProvable (Base := Base) (Const := Const) (.eq u v)) :
    HenkinProvable (Base := Base) (Const := Const) (.eq t v) := by
  rcases htu with ⟨Γ₁, hΓ₁, htu⟩
  rcases huv with ⟨Γ₂, hΓ₂, huv⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hΓ₁ ψ hψ
    · exact hΓ₂ ψ hψ
  · exact
      @ExtDerivation.eqTrans _ _ [] (Γ₁ ++ Γ₂) τ t u v
        (ExtDerivation.mono (by intro ψ hψ; exact List.mem_append_left _ hψ) htu)
        (ExtDerivation.mono (by intro ψ hψ; exact List.mem_append_right _ hψ) huv)

/--
If two closed cumulative-Henkin propositions have the same Henkin-world truth
set, then they are propositionally equal modulo the cumulative Henkin axioms.
-/
theorem henkinProvable_eq_prop_of_henkinTruthSet_eq
    {p q : ClosedFormula (HInf Base Const)}
    (hpq :
      henkinTruthSet (Base := Base) (Const := Const) p =
        henkinTruthSet (Base := Base) (Const := Const) q) :
    HenkinProvable (Base := Base) (Const := Const) (.eq p q) := by
  have hValid :
      CanonicalHenkinValidFrom (Base := Base) (Const := Const) [] (.eq p q) := by
    intro W hHenkin _hTop
    rw [mem_denoteFormula_empty_iff]
    apply W.mem_of_provable
    refine ClosedTheorySet.provable_of_closedTheory
      (Const := HInf Base Const)
      (T := W.carrier)
      (Δ := [.imp p q, .imp q p])
      ?_
      ?_
    · intro ψ hψ
      simp at hψ
      rcases hψ with rfl | rfl
      · exact
          (forcesImp_iff_mem
            (Base := Base)
            (Const := Const)
            (W := W)
            hHenkin
            (φ := p)
            (ψ := q)).1
            (by
              intro V hWV hpV
              let Vh : HenkinWorld Base Const :=
                ⟨V, by
                  intro χ hχ
                  exact hWV (hHenkin hχ)⟩
              have hpVh :
                  Vh ∈ henkinTruthSet (Base := Base) (Const := Const) p := hpV
              have hqVh :
                  Vh ∈ henkinTruthSet (Base := Base) (Const := Const) q := by
                simpa [hpq] using hpVh
              exact hqVh)
      · exact
          (forcesImp_iff_mem
            (Base := Base)
            (Const := Const)
            (W := W)
            hHenkin
            (φ := q)
            (ψ := p)).1
            (by
              intro V hWV hqV
              let Vh : HenkinWorld Base Const :=
                ⟨V, by
                  intro χ hχ
                  exact hWV (hHenkin hχ)⟩
              have hqVh :
                  Vh ∈ henkinTruthSet (Base := Base) (Const := Const) q := hqV
              have hpVh :
                  Vh ∈ henkinTruthSet (Base := Base) (Const := Const) p := by
                simpa [hpq] using hqVh
              exact hpVh)
    · exact
        ExtDerivation.eqPropI
          (ExtDerivation.hyp
            (Δ := [.imp p q, .imp q p])
            (φ := .imp p q)
            (by simp))
          (ExtDerivation.hyp
            (Δ := [.imp p q, .imp q p])
            (φ := .imp q p)
            (by simp))
  have hProv' :
      ClosedTheorySet.Provable
        (Const := HInf Base Const)
        (fun ψ =>
          ψ ∈ ([] : List (ClosedFormula (HInf Base Const))) ∨
            ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
        (.eq p q) :=
    (canonicalHenkinValidFrom_iff_provable
      (Base := Base)
      (Const := Const)
      (Δ := [])
      (φ := .eq p q)).1 hValid
  exact
    ClosedTheorySet.provable_mono
      (Const := HInf Base Const)
      (T := fun ψ =>
        ψ ∈ ([] : List (ClosedFormula (HInf Base Const))) ∨
          ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
      (U := HenkinAxioms (Base := Base) (Const := Const))
      (by
        intro ψ hψ
        simpa using hψ)
      hProv'

/-- Recursive semantic values carried by the represented canonical bridge. -/
def RepresentedCarrier (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max u (v + 1))
  | .prop => HenkinTruthVal Base Const
  | .base b => ClosedTerm (HInf Base Const) (.base b)
  | .arr σ τ => RepresentedCarrier Base Const σ → RepresentedCarrier Base Const τ

/--
`Represents τ t x` says that the closed cumulative-Henkin term `t` represents
the semantic value `x` at type `τ`.

Positive example:
- at proposition type, the representative is the Henkin-world truth set of a
  closed formula;
- at base types, representatives are tracked up to equality provable from the
  cumulative Henkin axioms.

Negative example:
- at function type, representation is not raw meta-level equality of functions;
  it is extensional behavior on represented inputs.
-/
def Represents :
    (τ : Ty Base) →
      ClosedTerm (HInf Base Const) τ →
      RepresentedCarrier Base Const τ →
        Prop
  | .prop, φ, p =>
      (show HenkinTruthVal Base Const from
          henkinTruthSet (Base := Base) (Const := Const) φ) = p
  | .base _, t, x =>
      HenkinProvable (Base := Base) (Const := Const) (.eq t x)
  | .arr σ τ, t, f =>
      ∀ ⦃u : ClosedTerm (HInf Base Const) σ⦄
        ⦃x : RepresentedCarrier Base Const σ⦄,
        Represents σ u x →
          Represents τ (.app t u) (f x)
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

/--
Recursive code equality for represented values.

Positive example:
- at proposition and base types, this is Henkin-axiom provable equality;
- at function type, two codes are equal when they produce equal output codes on
  every represented input.

Negative example:
- this is not yet the final semantic equality used by the standard model bridge;
  it is the code-level logical relation that makes representative choice honest.
-/
def CodeEq :
    (τ : Ty Base) →
      ClosedTerm (HInf Base Const) τ →
      ClosedTerm (HInf Base Const) τ →
        Prop
  | .prop, p, q => HenkinProvable (Base := Base) (Const := Const) (.eq p q)
  | .base _, t, u => HenkinProvable (Base := Base) (Const := Const) (.eq t u)
  | .arr σ τ, f, g =>
      ∀ ⦃u : ClosedTerm (HInf Base Const) σ⦄
        ⦃x : RepresentedCarrier Base Const σ⦄,
        Represents (Base := Base) (Const := Const) σ u x →
          CodeEq τ (.app f u) (.app g u)
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

/-- Admissible represented values are exactly those that have a closed code. -/
def Admissible (τ : Ty Base) (x : RepresentedCarrier Base Const τ) : Prop :=
  ∃ t : ClosedTerm (HInf Base Const) τ, Represents (Base := Base) (Const := Const) τ t x

/-- Typed valuations into represented canonical values. -/
abbrev Valuation (Γ : Ctx Base) :=
  ∀ {τ : Ty Base}, Var Γ τ → RepresentedCarrier Base Const τ

/-- A represented valuation is admissible when every variable has a closed code. -/
def ValuationAdmissible {Γ : Ctx Base} (ρ : Valuation (Base := Base) (Const := Const) Γ) : Prop :=
  ∀ {τ : Ty Base} (v : Var Γ τ),
    Admissible (Base := Base) (Const := Const) τ (ρ v)

/--
`SubstRep σs ρ` says that the closed substitution `σs` codes the represented
valuation `ρ` pointwise.
-/
def SubstRep {Γ : Ctx Base}
    (σs : ClosedSubst Base Const Γ)
    (ρ : Valuation (Base := Base) (Const := Const) Γ) : Prop :=
  ∀ {τ : Ty Base} (v : Var Γ τ),
    Represents (Base := Base) (Const := Const) τ (σs v) (ρ v)

/-- Extend a represented valuation by one more semantic value. -/
def Valuation.extend
    {Γ : Ctx Base}
    (ρ : Valuation (Base := Base) (Const := Const) Γ)
    (x : RepresentedCarrier Base Const σ) :
    Valuation (Base := Base) (Const := Const) (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

@[simp] theorem represents_prop_iff
    {φ : ClosedFormula (HInf Base Const)}
    {p : RepresentedCarrier Base Const .prop} :
    Represents (Base := Base) (Const := Const) .prop φ p ↔
      henkinTruthSet (Base := Base) (Const := Const) φ = p :=
  by simp [Represents]

@[simp] theorem represents_base_iff
    {b : Base}
    {t : ClosedTerm (HInf Base Const) (.base b)}
    {x : RepresentedCarrier Base Const (.base b)} :
    Represents (Base := Base) (Const := Const) (.base b) t x ↔
      HenkinProvable (Base := Base) (Const := Const) (.eq t x) :=
  by simp [Represents]

@[simp] theorem represents_arr_iff
    {σ τ : Ty Base}
    {t : ClosedTerm (HInf Base Const) (σ ⇒ τ)}
    {f : RepresentedCarrier Base Const (σ ⇒ τ)} :
    Represents (Base := Base) (Const := Const) (σ ⇒ τ) t f ↔
      ∀ ⦃u : ClosedTerm (HInf Base Const) σ⦄
        ⦃x : RepresentedCarrier Base Const σ⦄,
        Represents (Base := Base) (Const := Const) σ u x →
          Represents (Base := Base) (Const := Const) τ (.app t u) (f x) :=
  by simp [Represents]

@[simp] theorem codeEq_prop_iff
    {p q : ClosedFormula (HInf Base Const)} :
    CodeEq (Base := Base) (Const := Const) .prop p q ↔
      HenkinProvable (Base := Base) (Const := Const) (.eq p q) :=
  by simp [CodeEq]

@[simp] theorem codeEq_base_iff
    {b : Base}
    {t u : ClosedTerm (HInf Base Const) (.base b)} :
    CodeEq (Base := Base) (Const := Const) (.base b) t u ↔
      HenkinProvable (Base := Base) (Const := Const) (.eq t u) :=
  by simp [CodeEq]

@[simp] theorem codeEq_arr_iff
    {σ τ : Ty Base}
    {f g : ClosedTerm (HInf Base Const) (σ ⇒ τ)} :
    CodeEq (Base := Base) (Const := Const) (σ ⇒ τ) f g ↔
      ∀ ⦃u : ClosedTerm (HInf Base Const) σ⦄
        ⦃x : RepresentedCarrier Base Const σ⦄,
        Represents (Base := Base) (Const := Const) σ u x →
          CodeEq (Base := Base) (Const := Const) τ (.app f u) (.app g u) :=
  by simp [CodeEq]

/--
Closed equality provable from the cumulative Henkin axioms induces the
recursive code-level equality relation.

Positive example:
- at base and proposition types this is immediate, since `CodeEq` is just the
  corresponding Henkin-provable equality;
- at function type this reuses extensional HOL's application congruence rule,
  reducing pointwise code equality to the smaller result type.

Negative example:
- this only transports syntactic equality into `CodeEq`; the converse direction
  still needs a stronger represented-input theorem and is not assumed here.
-/
theorem codeEq_of_henkinProvable_eq :
    ∀ {τ : Ty Base}
      {t u : ClosedTerm (HInf Base Const) τ},
      HenkinProvable (Base := Base) (Const := Const) (.eq t u) →
        CodeEq (Base := Base) (Const := Const) τ t u
  | .prop, t, u, htu => by
      simpa [CodeEq] using htu
  | .base b, t, u, htu => by
      simpa [CodeEq] using htu
  | .arr σ τ, t, u, htu => by
      rw [codeEq_arr_iff]
      intro v x hx
      rcases htu with ⟨Γ, hΓ, hDeriv⟩
      refine codeEq_of_henkinProvable_eq ?_
      exact ⟨Γ, hΓ, ExtDerivation.eqApp v hDeriv⟩

theorem represents_app
    {σ τ : Ty Base}
    {t : ClosedTerm (HInf Base Const) (σ ⇒ τ)}
    {f : RepresentedCarrier Base Const (σ ⇒ τ)}
    {u : ClosedTerm (HInf Base Const) σ}
    {x : RepresentedCarrier Base Const σ}
    (ht : Represents (Base := Base) (Const := Const) (σ ⇒ τ) t f)
    (hx : Represents (Base := Base) (Const := Const) σ u x) :
    Represents (Base := Base) (Const := Const) τ (.app t u) (f x) :=
  (represents_arr_iff (Base := Base) (Const := Const)).1 ht hx

theorem admissible_iff_exists_rep
    {τ : Ty Base}
    {x : RepresentedCarrier Base Const τ} :
    Admissible (Base := Base) (Const := Const) τ x ↔
      ∃ t : ClosedTerm (HInf Base Const) τ,
        Represents (Base := Base) (Const := Const) τ t x :=
  Iff.rfl

theorem valuationAdmissible_of_substRep
    {Γ : Ctx Base}
    {σs : ClosedSubst Base Const Γ}
    {ρ : Valuation (Base := Base) (Const := Const) Γ}
    (hρ : SubstRep (Base := Base) (Const := Const) σs ρ) :
    ValuationAdmissible (Base := Base) (Const := Const) ρ := by
  intro τ v
  exact ⟨σs v, hρ v⟩

theorem admissible_truthSet
    (φ : ClosedFormula (HInf Base Const)) :
    Admissible (Base := Base) (Const := Const) .prop
      (show HenkinTruthVal Base Const from
        henkinTruthSet (Base := Base) (Const := Const) φ) :=
  ⟨φ, (represents_prop_iff (Base := Base) (Const := Const)).2 rfl⟩

theorem admissible_base
    {b : Base}
    (t : ClosedTerm (HInf Base Const) (.base b)) :
    Admissible (Base := Base) (Const := Const) (.base b) t :=
  ⟨t, (represents_base_iff (Base := Base) (Const := Const)).2 <|
    henkinProvable_of_theorem (Base := Base) (Const := Const) (.eqRefl t)⟩

theorem henkinProvable_eqPropEL
    {p q : ClosedFormula (HInf Base Const)}
    (hpq : HenkinProvable (Base := Base) (Const := Const) (.eq p q)) :
    HenkinProvable (Base := Base) (Const := Const) (.imp p q) := by
  rcases hpq with ⟨Γ, hΓ, hDeriv⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqPropEL hDeriv⟩

theorem henkinProvable_eqPropER
    {p q : ClosedFormula (HInf Base Const)}
    (hpq : HenkinProvable (Base := Base) (Const := Const) (.eq p q)) :
    HenkinProvable (Base := Base) (Const := Const) (.imp q p) := by
  rcases hpq with ⟨Γ, hΓ, hDeriv⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqPropER hDeriv⟩

theorem represents_prop_of_henkinProvable_eq
    {p q : ClosedFormula (HInf Base Const)}
    {x : RepresentedCarrier Base Const .prop}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hpq : HenkinProvable (Base := Base) (Const := Const) (.eq p q)) :
    Represents (Base := Base) (Const := Const) .prop q x := by
  rw [represents_prop_iff] at hp ⊢
  have hpq' :
      henkinTruthSet (Base := Base) (Const := Const) p =
        henkinTruthSet (Base := Base) (Const := Const) q := by
    ext W
    constructor
    · intro hW
      have hImp :
          (.imp p q : ClosedFormula (HInf Base Const)) ∈ W.1.carrier := by
        exact W.1.mem_of_provable <|
          ClosedTheorySet.provable_mono
            (Const := HInf Base Const)
            (T := HenkinAxioms (Base := Base) (Const := Const))
            (U := W.1.carrier)
            (by
              intro ψ hψ
              exact W.2 hψ)
            (henkinProvable_eqPropEL (Base := Base) (Const := Const) hpq)
      exact W.1.mp hImp hW
    · intro hW
      have hImp :
          (.imp q p : ClosedFormula (HInf Base Const)) ∈ W.1.carrier := by
        exact W.1.mem_of_provable <|
          ClosedTheorySet.provable_mono
            (Const := HInf Base Const)
            (T := HenkinAxioms (Base := Base) (Const := Const))
            (U := W.1.carrier)
            (by
              intro ψ hψ
              exact W.2 hψ)
            (henkinProvable_eqPropER (Base := Base) (Const := Const) hpq)
      exact W.1.mp hImp hW
  exact hpq'.symm.trans hp

theorem henkinProvable_eq_prop_of_represents_same
    {p q : ClosedFormula (HInf Base Const)}
    {x : RepresentedCarrier Base Const .prop}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hq : Represents (Base := Base) (Const := Const) .prop q x) :
    HenkinProvable (Base := Base) (Const := Const) (.eq p q) := by
  rw [represents_prop_iff] at hp hq
  exact
    henkinProvable_eq_prop_of_henkinTruthSet_eq
      (Base := Base)
      (Const := Const)
      (hp.trans hq.symm)

theorem henkinProvable_eq_base_of_represents_same
    {b : Base}
    {t u : ClosedTerm (HInf Base Const) (.base b)}
    {x : RepresentedCarrier Base Const (.base b)}
    (ht : Represents (Base := Base) (Const := Const) (.base b) t x)
    (hu : Represents (Base := Base) (Const := Const) (.base b) u x) :
    HenkinProvable (Base := Base) (Const := Const) (.eq t u) := by
  rw [represents_base_iff] at ht hu
  exact
    henkinProvable_eq_trans
      (Base := Base)
      (Const := Const)
      ht
      (henkinProvable_eq_symm (Base := Base) (Const := Const) hu)

theorem codeEq_of_represents_same :
    ∀ {τ : Ty Base}
      {t u : ClosedTerm (HInf Base Const) τ}
      {x : RepresentedCarrier Base Const τ},
      Represents (Base := Base) (Const := Const) τ t x →
      Represents (Base := Base) (Const := Const) τ u x →
        CodeEq (Base := Base) (Const := Const) τ t u
  | .prop, t, u, x, ht, hu =>
      by
        simpa [CodeEq] using
          (henkinProvable_eq_prop_of_represents_same
            (Base := Base)
            (Const := Const)
            ht
            hu)
  | .base b, t, u, x, ht, hu =>
      by
        simpa [CodeEq] using
          (henkinProvable_eq_base_of_represents_same
            (Base := Base)
            (Const := Const)
            (b := b)
            ht
            hu)
  | .arr σ τ, t, u, f, ht, hu => by
      rw [codeEq_arr_iff]
      intro v x hx
      exact
        codeEq_of_represents_same
          ((represents_arr_iff (Base := Base) (Const := Const)).1 ht hx)
          ((represents_arr_iff (Base := Base) (Const := Const)).1 hu hx)

theorem represents_of_codeEq_left :
    ∀ {τ : Ty Base}
      {t u : ClosedTerm (HInf Base Const) τ}
      {x : RepresentedCarrier Base Const τ},
      CodeEq (Base := Base) (Const := Const) τ t u →
      Represents (Base := Base) (Const := Const) τ t x →
        Represents (Base := Base) (Const := Const) τ u x
  | .prop, t, u, x, htu, htx =>
      represents_prop_of_henkinProvable_eq
        (Base := Base)
        (Const := Const)
        htx
        (by simpa [CodeEq] using htu)
  | .base b, t, u, x, htu, htx => by
      rw [represents_base_iff] at htx ⊢
      exact
        henkinProvable_eq_trans
          (Base := Base)
          (Const := Const)
          (henkinProvable_eq_symm
            (Base := Base)
            (Const := Const)
            (by simpa [CodeEq] using htu))
          htx
  | .arr σ τ, t, u, f, htu, htf => by
      rw [represents_arr_iff] at htf ⊢
      rw [codeEq_arr_iff] at htu
      intro v x hv
      exact represents_of_codeEq_left (htu hv) (htf hv)

theorem substRep_extend
    {Γ : Ctx Base}
    {σs : ClosedSubst Base Const Γ}
    {ρ : Valuation (Base := Base) (Const := Const) Γ}
    {t : ClosedTerm (HInf Base Const) σ}
    {x : RepresentedCarrier Base Const σ}
    (hρ : SubstRep (Base := Base) (Const := Const) σs ρ)
    (hx : Represents (Base := Base) (Const := Const) σ t x) :
    SubstRep
      (Base := Base)
      (Const := Const)
      (ClosedSubst.extend (Base := Base) (Const := Const) σs t)
      (Valuation.extend (Base := Base) (Const := Const) ρ x) := by
  intro τ v
  cases v with
  | vz =>
      simpa [ClosedSubst.extend, Valuation.extend] using hx
  | vs v =>
      simpa [ClosedSubst.extend, Valuation.extend] using hρ v

@[simp] theorem subst_extend_eq_instantiate_term
    {Γ : Ctx Base} {σ τ : Ty Base}
    (t : Term (HInf Base Const) (σ :: Γ) τ)
    (σs : ClosedSubst Base Const Γ)
    (u : ClosedTerm (HInf Base Const) σ) :
    subst (ClosedSubst.extend (Base := Base) (Const := Const) σs u) t =
      instantiate (Base := Base) u
        (subst (Subst.lift (Base := Base) (σ := σ) σs) t) := by
  calc
    subst (ClosedSubst.extend (Base := Base) (Const := Const) σs u) t
        =
        subst
          (Subst.comp
            (Subst.single (Base := Base) (Const := HInf Base Const) u)
            (Subst.lift (Base := Base) (σ := σ) σs))
          t := by
            apply subst_ext
            intro ρ v
            cases v with
            | vz =>
                rfl
            | vs v =>
                simpa [ClosedSubst.extend, Subst.comp, instantiate, weaken] using
                  (instantiate_weaken
                    (Base := Base)
                    (Const := HInf Base Const)
                    (t := u)
                    (u := σs v)).symm
    _ =
        subst
          (Subst.single (Base := Base) (Const := HInf Base Const) u)
          (subst (Subst.lift (Base := Base) (σ := σ) σs) t) := by
            symm
            exact subst_comp
              (Base := Base)
              (Const := HInf Base Const)
              (τs := Subst.single (Base := Base) (Const := HInf Base Const) u)
              (σs := Subst.lift (Base := Base) (σ := σ) σs)
              (t := t)

/-- Canonical default closed code at any type, used only outside admissible input. -/
noncomputable def defaultCode (τ : Ty Base) :
    ClosedTerm (HInf Base Const) τ :=
  witnessTerm (Base := Base) (Const := Const) τ

/-- Choose one closed representative from an admissibility witness. -/
noncomputable def someCode
    {τ : Ty Base}
    {x : RepresentedCarrier Base Const τ}
    (h : Admissible (Base := Base) (Const := Const) τ x) :
    ClosedTerm (HInf Base Const) τ :=
  Classical.choose h

theorem someCode_represents
    {τ : Ty Base}
    {x : RepresentedCarrier Base Const τ}
    (h : Admissible (Base := Base) (Const := Const) τ x) :
    Represents (Base := Base) (Const := Const) τ (someCode h) x :=
  Classical.choose_spec h

/--
Total code selection: use an actual representative on admissible inputs and the
canonical default closed witness otherwise.

Positive example:
- later function decoding can apply a coded function to `chooseCode x`.

Negative example:
- this choice alone does not yet prove independence from the chosen
  representative; that is the next theorem layer.
-/
noncomputable def chooseCode
    {τ : Ty Base}
    (x : RepresentedCarrier Base Const τ) :
    ClosedTerm (HInf Base Const) τ :=
  by
    classical
    exact
      if h : Admissible (Base := Base) (Const := Const) τ x then
        someCode (Base := Base) (Const := Const) h
      else
        defaultCode (Base := Base) (Const := Const) τ

theorem chooseCode_represents
    {τ : Ty Base}
    {x : RepresentedCarrier Base Const τ}
    (h : Admissible (Base := Base) (Const := Const) τ x) :
    Represents (Base := Base) (Const := Const) τ (chooseCode (Base := Base) (Const := Const) x) x := by
  classical
  simp [chooseCode, h, someCode_represents]

/-- Any representing code makes its semantic value admissible. -/
theorem admissible_of_represents
    {τ : Ty Base}
    {t : ClosedTerm (HInf Base Const) τ}
    {x : RepresentedCarrier Base Const τ}
    (ht : Represents (Base := Base) (Const := Const) τ t x) :
    Admissible (Base := Base) (Const := Const) τ x :=
  ⟨t, ht⟩

/-- Interpret a closed cumulative-Henkin code as its canonical represented input. -/
noncomputable def representedInput :
    {τ : Ty Base} →
      ClosedTerm (HInf Base Const) τ →
        RepresentedCarrier Base Const τ
  | .prop, p => henkinTruthSet (Base := Base) (Const := Const) p
  | .base _, t => t
  | .arr σ τ, f => fun x =>
      representedInput (.app f (chooseCode (Base := Base) (Const := Const) x))
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

mutual

/-- Every closed cumulative-Henkin code represents its own canonical represented input. -/
theorem representedInput_spec :
    ∀ {τ : Ty Base} (t : ClosedTerm (HInf Base Const) τ),
      Represents (Base := Base) (Const := Const) τ t
        (representedInput (Base := Base) (Const := Const) t)
  | .prop, p => by
      simpa [representedInput] using
        ((represents_prop_iff (Base := Base) (Const := Const)).2 rfl)
  | .base b, t => by
      simpa [representedInput] using
        ((represents_base_iff (Base := Base) (Const := Const)).2 <|
          henkinProvable_of_theorem (Base := Base) (Const := Const) (.eqRefl t))
  | .arr σ τ, f => by
      rw [represents_arr_iff]
      intro u x hx
      have hxAdm :
          Admissible (Base := Base) (Const := Const) σ x :=
        admissible_of_represents (Base := Base) (Const := Const) hx
      have hChoose :
          Represents (Base := Base) (Const := Const) σ
            (chooseCode (Base := Base) (Const := Const) x) x :=
        chooseCode_represents (Base := Base) (Const := Const) hxAdm
      have hCodeArg :
          CodeEq (Base := Base) (Const := Const) σ
            (chooseCode (Base := Base) (Const := Const) x) u :=
        codeEq_of_represents_same
          (Base := Base)
          (Const := Const)
          hChoose
          hx
      have hEqArg :
          HenkinProvable (Base := Base) (Const := Const)
            (.eq
              (chooseCode (Base := Base) (Const := Const) x)
              u) :=
        henkinProvable_eq_of_codeEq hCodeArg
      have hCodeOut :
          CodeEq (Base := Base) (Const := Const) τ
            (.app f (chooseCode (Base := Base) (Const := Const) x))
            (.app f u) := by
        apply codeEq_of_henkinProvable_eq (Base := Base) (Const := Const)
        rcases hEqArg with ⟨Γ, hΓ, hDeriv⟩
        exact ⟨Γ, hΓ, ExtDerivation.eqAppArg f hDeriv⟩
      have hRepChoose :
          Represents (Base := Base) (Const := Const) τ
            (.app f (chooseCode (Base := Base) (Const := Const) x))
            (representedInput
              (.app f (chooseCode (Base := Base) (Const := Const) x))) :=
        representedInput_spec (.app f (chooseCode (Base := Base) (Const := Const) x))
      simpa [representedInput] using
        (represents_of_codeEq_left
          (Base := Base)
          (Const := Const)
          hCodeOut
          hRepChoose)

/-- Recursive code equality can be collapsed back to Henkin-provable equality. -/
theorem henkinProvable_eq_of_codeEq :
    ∀ {τ : Ty Base} {t u : ClosedTerm (HInf Base Const) τ},
      CodeEq (Base := Base) (Const := Const) τ t u →
        HenkinProvable (Base := Base) (Const := Const) (.eq t u)
  | .prop, t, u, htu => by
      simpa [CodeEq] using htu
  | .base b, t, u, htu => by
      simpa [CodeEq] using htu
  | .arr σ τ, t, u, htu => by
      let body : Formula (HInf Base Const) (σ :: ([] : Ctx Base)) :=
        .eq
          (.app (weaken (Base := Base) (Const := HInf Base Const) (σ := σ) t) (.var .vz))
          (.app (weaken (Base := Base) (Const := HInf Base Const) (σ := σ) u) (.var .vz))
      rw [codeEq_arr_iff] at htu
      have hValid :
          CanonicalHenkinValidFrom (Base := Base) (Const := Const) [] (.eq t u) := by
        intro W hHenkin _hTop
        rw [mem_denoteFormula_empty_iff]
        have hAll :
            W ∈ denoteFormula (Base := Base) (Const := Const) (.all body)
              (emptyClosedSubst Base Const) := by
          rw [mem_denoteFormula_all_iff]
          intro c
          have hCodeAt :
              CodeEq (Base := Base) (Const := Const) τ
                (.app t c)
                (.app u c) :=
            htu (representedInput_spec c)
          have hEqAt :
              HenkinProvable (Base := Base) (Const := Const)
                (.eq (.app t c) (.app u c)) :=
            henkinProvable_eq_of_codeEq hCodeAt
          have hEqAtW :
              (.eq (.app t c) (.app u c) : ClosedFormula (HInf Base Const)) ∈ W.carrier := by
            exact
              W.mem_of_provable <|
                ClosedTheorySet.provable_mono
                  (Const := HInf Base Const)
                  (T := HenkinAxioms (Base := Base) (Const := Const))
                  (U := W.carrier)
                  (by
                    intro ψ hψ
                    exact hHenkin hψ)
                  hEqAt
          have hBodyEval :
              instantiate (Base := Base) c
                (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const)) body) =
              (.eq (.app t c) (.app u c) : ClosedFormula (HInf Base Const)) := by
            have hAppLeft :
                subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                  (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t)) = t := by
              have hLiftEmpty_weaken :
                  subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t) =
                  rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t := by
                simpa [subst_id] using
                  (subst_ext
                    (Const := HInf Base Const)
                    (Γ := σ :: ([] : Ctx Base))
                    (Δ := σ :: ([] : Ctx Base))
                    (ρ := σ ⇒ τ)
                    (σs := Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (τs := Subst.id (Base := Base) (Const := HInf Base Const)
                      (Γ := σ :: ([] : Ctx Base)))
                    (fun {τ'} v => by
                      cases v with
                      | vz => rfl
                      | vs v => cases v)
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t))
              calc
                subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                    (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                      (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t))
                    =
                    subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                      (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) t) := by
                        rw [hLiftEmpty_weaken]
                _ = t := by
                    simpa [instantiate, weaken] using
                      (instantiate_weaken (Base := Base) (Const := HInf Base Const) c t)
            have hAppRight :
                subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                  (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u)) = u := by
              have hLiftEmpty_weaken :
                  subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u) =
                  rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u := by
                simpa [subst_id] using
                  (subst_ext
                    (Const := HInf Base Const)
                    (Γ := σ :: ([] : Ctx Base))
                    (Δ := σ :: ([] : Ctx Base))
                    (ρ := σ ⇒ τ)
                    (σs := Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (τs := Subst.id (Base := Base) (Const := HInf Base Const)
                      (Γ := σ :: ([] : Ctx Base)))
                    (fun {τ'} v => by
                      cases v with
                      | vz => rfl
                      | vs v => cases v)
                    (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u))
              calc
                subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                    (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                      (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u))
                    =
                    subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                      (rename (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ)) u) := by
                        rw [hLiftEmpty_weaken]
                _ = u := by
                    simpa [instantiate, weaken] using
                      (instantiate_weaken (Base := Base) (Const := HInf Base Const) c u)
            have hVar :
                subst (Subst.single (Base := Base) (Const := HInf Base Const) c)
                  ((Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    (Var.vz : Var (σ :: ([] : Ctx Base)) σ)) = c := by
              rfl
            change
                instantiate (Base := Base) c
                  (subst (Subst.lift (Base := Base) (σ := σ) (emptyClosedSubst Base Const))
                    ((.eq
                      (.app (weaken (Base := Base) (Const := HInf Base Const) (σ := σ) t)
                        (.var .vz))
                      (.app (weaken (Base := Base) (Const := HInf Base Const) (σ := σ) u)
                        (.var .vz))) :
                      Formula (HInf Base Const) (σ :: ([] : Ctx Base)))) =
              (.eq (.app t c) (.app u c) : ClosedFormula (HInf Base Const))
            simp [instantiate, weaken, subst, hAppLeft, hAppRight, hVar]
          rw [mem_denoteFormula_extend_iff]
          rw [hBodyEval]
          exact hEqAtW
        have hAllMem :
            (.all body : ClosedFormula (HInf Base Const)) ∈ W.carrier :=
          (mem_denoteFormula_empty_iff
            (Base := Base)
            (Const := Const)
            (W := W)
            (φ := .all body)).1 hAll
        have hEqProvW :
            ClosedTheorySet.Provable
              (Const := HInf Base Const)
              W.carrier
              (.eq t u) := by
          refine
            ClosedTheorySet.provable_of_closedTheory
              (Const := HInf Base Const)
              (T := W.carrier)
              (Δ := [.all body])
              ?_
              ?_
          · intro ψ hψ
            rcases List.mem_singleton.mp hψ with rfl
            exact hAllMem
          · exact
              ExtDerivation.funExt
                (ExtDerivation.hyp
                  (Δ := [.all body])
                  (φ := (.all body : ClosedFormula (HInf Base Const)))
                  (by simp))
        exact W.mem_of_provable hEqProvW
      have hProv' :
          ClosedTheorySet.Provable
            (Const := HInf Base Const)
            (fun ψ =>
              ψ ∈ ([] : List (ClosedFormula (HInf Base Const))) ∨
                ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
            (.eq t u) :=
        (canonicalHenkinValidFrom_iff_provable
          (Base := Base)
          (Const := Const)
          (Δ := [])
          (φ := .eq t u)).1 hValid
      simpa using hProv'

end

/-- Recursive code equality is symmetric. -/
theorem codeEq_symm :
    ∀ {τ : Ty Base}
      {t u : ClosedTerm (HInf Base Const) τ},
      CodeEq (Base := Base) (Const := Const) τ t u →
        CodeEq (Base := Base) (Const := Const) τ u t
  | .prop, t, u, htu => by
      simpa [CodeEq] using
        (henkinProvable_eq_symm (Base := Base) (Const := Const)
          (by simpa [CodeEq] using htu))
  | .base b, t, u, htu => by
      simpa [CodeEq] using
        (henkinProvable_eq_symm (Base := Base) (Const := Const)
          (by simpa [CodeEq] using htu))
  | .arr σ τ, t, u, htu => by
      rw [codeEq_arr_iff] at htu ⊢
      intro v x hx
      exact codeEq_symm (htu hx)

/-- Recursive code equality is transitive. -/
theorem codeEq_trans :
    ∀ {τ : Ty Base}
      {t u v : ClosedTerm (HInf Base Const) τ},
      CodeEq (Base := Base) (Const := Const) τ t u →
      CodeEq (Base := Base) (Const := Const) τ u v →
        CodeEq (Base := Base) (Const := Const) τ t v
  | .prop, t, u, v, htu, huv => by
      simpa [CodeEq] using
        (henkinProvable_eq_trans
          (Base := Base)
          (Const := Const)
          (by simpa [CodeEq] using htu)
          (by simpa [CodeEq] using huv))
  | .base b, t, u, v, htu, huv => by
      simpa [CodeEq] using
        (henkinProvable_eq_trans
          (Base := Base)
          (Const := Const)
          (by simpa [CodeEq] using htu)
          (by simpa [CodeEq] using huv))
  | .arr σ τ, t, u, v, htu, huv => by
      rw [codeEq_arr_iff] at htu huv ⊢
      intro w x hx
      exact codeEq_trans (htu hx) (huv hx)

/-- Changing the argument by `CodeEq` preserves code equality after application. -/
theorem codeEq_appArg_of_codeEq
    {σ τ : Ty Base}
    {f : ClosedTerm (HInf Base Const) (σ ⇒ τ)}
    {u v : ClosedTerm (HInf Base Const) σ}
    (huv : CodeEq (Base := Base) (Const := Const) σ u v) :
    CodeEq (Base := Base) (Const := Const) τ (.app f u) (.app f v) := by
  apply codeEq_of_henkinProvable_eq (Base := Base) (Const := Const)
  rcases henkinProvable_eq_of_codeEq (Base := Base) (Const := Const) huv with ⟨Γ, hΓ, hDeriv⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqAppArg f hDeriv⟩

/-- Function and argument `CodeEq` combine into application `CodeEq`. -/
theorem codeEq_appCongr_of_codeEq
    {σ τ : Ty Base}
    {f g : ClosedTerm (HInf Base Const) (σ ⇒ τ)}
    {u v : ClosedTerm (HInf Base Const) σ}
    (hfg : CodeEq (Base := Base) (Const := Const) (σ ⇒ τ) f g)
    (huv : CodeEq (Base := Base) (Const := Const) σ u v) :
    CodeEq (Base := Base) (Const := Const) τ (.app f u) (.app g v) := by
  rw [codeEq_arr_iff] at hfg
  exact
    codeEq_trans
      (hfg (representedInput_spec u))
      (codeEq_appArg_of_codeEq (Base := Base) (Const := Const) (f := g) huv)

/-- `CodeEq` transports representation from right to left as well. -/
theorem represents_of_codeEq_right :
    ∀ {τ : Ty Base}
      {t u : ClosedTerm (HInf Base Const) τ}
      {x : RepresentedCarrier Base Const τ},
      CodeEq (Base := Base) (Const := Const) τ t u →
      Represents (Base := Base) (Const := Const) τ u x →
        Represents (Base := Base) (Const := Const) τ t x
  | _, _, _, _, htu, hux =>
      represents_of_codeEq_left
        (Base := Base)
        (Const := Const)
        (codeEq_symm (Base := Base) (Const := Const) htu)
        hux

/-- Any representing code is canonically equal to `chooseCode` of the semantic
value it represents. -/
theorem codeEq_chooseCode_of_represents
    {τ : Ty Base}
    {t : ClosedTerm (HInf Base Const) τ}
    {x : RepresentedCarrier Base Const τ}
    (ht : Represents (Base := Base) (Const := Const) τ t x) :
    CodeEq (Base := Base) (Const := Const) τ t
      (chooseCode (Base := Base) (Const := Const) x) := by
  exact
    codeEq_of_represents_same
      (Base := Base)
      (Const := Const)
      ht
      (chooseCode_represents
        (Base := Base)
        (Const := Const)
        (admissible_of_represents (Base := Base) (Const := Const) ht))

/-- Conversely, `chooseCode` represents any value up to `CodeEq`. -/
theorem represents_of_codeEq_chooseCode
    {τ : Ty Base}
    {t : ClosedTerm (HInf Base Const) τ}
    {x : RepresentedCarrier Base Const τ}
    (ht : Represents (Base := Base) (Const := Const) τ t x) :
    Represents (Base := Base) (Const := Const) τ
      (chooseCode (Base := Base) (Const := Const) x) x ∧
      Represents (Base := Base) (Const := Const) τ t x := by
  refine ⟨?_, ht⟩
  exact chooseCode_represents
    (Base := Base)
    (Const := Const)
    (admissible_of_represents (Base := Base) (Const := Const) ht)

/-- Admissible represented functions send admissible inputs to admissible outputs. -/
theorem admissible_app
    {σ τ : Ty Base}
    {f : RepresentedCarrier Base Const (σ ⇒ τ)}
    {x : RepresentedCarrier Base Const σ}
    (hf : Admissible (Base := Base) (Const := Const) (σ ⇒ τ) f)
    (hx : Admissible (Base := Base) (Const := Const) σ x) :
    Admissible (Base := Base) (Const := Const) τ (f x) := by
  rcases hf with ⟨t, ht⟩
  rcases hx with ⟨u, hu⟩
  exact ⟨.app t u, represents_app (Base := Base) (Const := Const) ht hu⟩

/-- A represented function code sends any two codes of the same semantic input
to canonically equal output codes. -/
theorem codeEq_app_of_same_representation
    {σ τ : Ty Base}
    {f : ClosedTerm (HInf Base Const) (σ ⇒ τ)}
    {g : RepresentedCarrier Base Const (σ ⇒ τ)}
    {u v : ClosedTerm (HInf Base Const) σ}
    {x : RepresentedCarrier Base Const σ}
    (hf : Represents (Base := Base) (Const := Const) (σ ⇒ τ) f g)
    (hu : Represents (Base := Base) (Const := Const) σ u x)
    (hv : Represents (Base := Base) (Const := Const) σ v x) :
    CodeEq (Base := Base) (Const := Const) τ (.app f u) (.app f v) := by
  exact
    codeEq_of_represents_same
      (Base := Base)
      (Const := Const)
      (represents_app (Base := Base) (Const := Const) hf hu)
      (represents_app (Base := Base) (Const := Const) hf hv)

/-- Applying the chosen code of an admissible represented function to the
chosen code of an admissible input is canonically equal to the chosen code of
the semantic output. -/
theorem codeEq_app_chooseCode
    {σ τ : Ty Base}
    {f : RepresentedCarrier Base Const (σ ⇒ τ)}
    {x : RepresentedCarrier Base Const σ}
    (hf : Admissible (Base := Base) (Const := Const) (σ ⇒ τ) f)
    (hx : Admissible (Base := Base) (Const := Const) σ x) :
    CodeEq (Base := Base) (Const := Const) τ
      (.app
        (chooseCode (Base := Base) (Const := Const) f)
        (chooseCode (Base := Base) (Const := Const) x))
      (chooseCode (Base := Base) (Const := Const) (f x)) := by
  have hApp :
      Represents (Base := Base) (Const := Const) τ
        (.app
          (chooseCode (Base := Base) (Const := Const) f)
          (chooseCode (Base := Base) (Const := Const) x))
        (f x) := by
    exact
      represents_app
        (Base := Base)
        (Const := Const)
        (chooseCode_represents (Base := Base) (Const := Const) hf)
        (chooseCode_represents (Base := Base) (Const := Const) hx)
  exact
    codeEq_chooseCode_of_represents
      (Base := Base)
      (Const := Const)
      hApp

/-- External constant interpretation for the represented canonical premodel. -/
structure RepresentedConstDenotation
    (Base : Type u) (Const : Ty Base → Type v) where
  val :
    {τ : Ty Base} →
      HInf Base Const τ →
        RepresentedCarrier Base Const τ
  spec :
    ∀ {τ : Ty Base} (c : HInf Base Const τ),
      Represents (Base := Base) (Const := Const) τ (.const c) (val c)

/-- Canonical constant interpretation obtained by viewing each cumulative-Henkin
constant as its own represented input. -/
noncomputable def canonicalRepresentedConstDenotation :
    RepresentedConstDenotation Base Const where
  val := fun {τ} c =>
    representedInput (Base := Base) (Const := Const) (.const c)
  spec := by
    intro τ c
    simpa using
      (representedInput_spec
        (Base := Base)
        (Const := Const)
        (.const c))

/-- Base-type equality in the represented canonical premodel. -/
def representedBaseEq
    (b : Base)
    (t u : ClosedTerm (HInf Base Const) (.base b)) :
    HenkinTruthVal Base Const :=
  henkinTruthSet (Base := Base) (Const := Const) (.eq t u)

@[simp] theorem mem_representedBaseEq_iff
    {b : Base}
    {W : HenkinWorld Base Const}
    {t u : ClosedTerm (HInf Base Const) (.base b)} :
    W ∈ representedBaseEq (Base := Base) (Const := Const) b t u ↔
      (.eq t u : ClosedFormula (HInf Base Const)) ∈ W.1.carrier :=
  Iff.rfl

theorem representedBaseEq_refl
    {b : Base}
    (x : ClosedTerm (HInf Base Const) (.base b)) :
    representedBaseEq (Base := Base) (Const := Const) b x x = ⊥ := by
  ext W
  constructor
  · intro _h
    simp
  · intro _h
    exact
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
        (mem_eq_refl (Base := Base) (Const := Const) x W.1)

theorem representedBaseEq_symm
    {b : Base}
    (x y : ClosedTerm (HInf Base Const) (.base b)) :
    representedBaseEq (Base := Base) (Const := Const) b x y =
      representedBaseEq (Base := Base) (Const := Const) b y x := by
  ext W
  constructor <;> intro hxy
  · have hxy' :
        (.eq x y : ClosedFormula (HInf Base Const)) ∈ W.1.carrier :=
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).1 hxy
    have hProv :
        ClosedTheorySet.Provable
          (Const := HInf Base Const)
          W.1.carrier
          (.eq y x) := by
      refine
        ClosedTheorySet.provable_of_closedTheory
          (Const := HInf Base Const)
          (T := W.1.carrier)
          (Δ := [.eq x y])
          ?_
          ?_
      · intro ψ hψ
        rcases List.mem_singleton.mp hψ with rfl
        exact hxy'
      · exact
          ExtDerivation.eqSymm
            (ExtDerivation.hyp
              (Δ := [.eq x y])
              (φ := (.eq x y : ClosedFormula (HInf Base Const)))
              (by simp))
    exact
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
        (W.1.mem_of_provable hProv)
  · have hxy' :
        (.eq y x : ClosedFormula (HInf Base Const)) ∈ W.1.carrier :=
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).1 hxy
    have hProv :
        ClosedTheorySet.Provable
          (Const := HInf Base Const)
          W.1.carrier
          (.eq x y) := by
      refine
        ClosedTheorySet.provable_of_closedTheory
          (Const := HInf Base Const)
          (T := W.1.carrier)
          (Δ := [.eq y x])
          ?_
          ?_
      · intro ψ hψ
        rcases List.mem_singleton.mp hψ with rfl
        exact hxy'
      · exact
          ExtDerivation.eqSymm
            (ExtDerivation.hyp
              (Δ := [.eq y x])
              (φ := (.eq y x : ClosedFormula (HInf Base Const)))
              (by simp))
    exact
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
        (W.1.mem_of_provable hProv)

theorem mem_representedBaseEq_trans
    {b : Base}
    {W : HenkinWorld Base Const}
    {x y z : ClosedTerm (HInf Base Const) (.base b)}
    (hxy :
      W ∈ representedBaseEq (Base := Base) (Const := Const) b x y)
    (hyz :
      W ∈ representedBaseEq (Base := Base) (Const := Const) b y z) :
    W ∈ representedBaseEq (Base := Base) (Const := Const) b x z := by
  have hxy' :
      (.eq x y : ClosedFormula (HInf Base Const)) ∈ W.1.carrier :=
    (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).1 hxy
  have hyz' :
      (.eq y z : ClosedFormula (HInf Base Const)) ∈ W.1.carrier :=
    (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).1 hyz
  have hProv :
      ClosedTheorySet.Provable
        (Const := HInf Base Const)
        W.1.carrier
        (.eq x z) := by
    refine
      ClosedTheorySet.provable_of_closedTheory
        (Const := HInf Base Const)
        (T := W.1.carrier)
        (Δ := [.eq x y, .eq y z])
        ?_
        ?_
    · intro ψ hψ
      simp at hψ
      rcases hψ with rfl | rfl
      · exact hxy'
      · exact hyz'
    · exact
        ExtDerivation.eqTrans
          (ExtDerivation.hyp
            (Δ := [.eq x y, .eq y z])
            (φ := (.eq x y : ClosedFormula (HInf Base Const)))
            (by simp))
          (ExtDerivation.hyp
            (Δ := [.eq x y, .eq y z])
            (φ := (.eq y z : ClosedFormula (HInf Base Const)))
            (by simp))
  exact
    (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
      (W.1.mem_of_provable hProv)

/-- Order-theoretic transitivity form of `representedBaseEq`, aligned with the
reverse-inclusion order on `UpperSet`. -/
theorem representedBaseEq_trans_le
    {b : Base}
    (x y z : ClosedTerm (HInf Base Const) (.base b)) :
    representedBaseEq (Base := Base) (Const := Const) b x z ≤
      representedBaseEq (Base := Base) (Const := Const) b x y ⊔
        representedBaseEq (Base := Base) (Const := Const) b y z := by
  intro W hW
  change W ∈ representedBaseEq (Base := Base) (Const := Const) b x y ⊔
      representedBaseEq (Base := Base) (Const := Const) b y z at hW
  change W ∈ representedBaseEq (Base := Base) (Const := Const) b x z
  rw [UpperSet.mem_sup_iff] at hW
  exact mem_representedBaseEq_trans
    (Base := Base)
    (Const := Const)
    (W := W)
    hW.1
    hW.2

/--
Extensional semantic equality on represented canonical values.

Positive example:
- at proposition type this is bi-implication in the Henkin truth-value algebra;
- at base type this is the represented closed-term equality truth set.

Negative example:
- at function type this is not raw meta-level equality of functions;
  it quantifies only over admissible represented inputs.
-/
def RepEqv :
    (τ : Ty Base) →
      RepresentedCarrier Base Const τ →
      RepresentedCarrier Base Const τ →
        HenkinTruthVal Base Const
  | .prop, p, q =>
      ((show HenkinTruthVal Base Const from p) \
          (show HenkinTruthVal Base Const from q)) ⊔
        ((show HenkinTruthVal Base Const from q) \
          (show HenkinTruthVal Base Const from p))
  | .base b, x, y => representedBaseEq (Base := Base) (Const := Const) b x y
  | .arr σ τ, f, g =>
      sSup <|
        Set.range
          (fun x : {x : RepresentedCarrier Base Const σ //
              Admissible (Base := Base) (Const := Const) σ x} =>
            RepEqv τ (f x.1) (g x.1))
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

@[simp] theorem repEqv_prop
    {p q : HenkinTruthVal Base Const} :
    RepEqv (Base := Base) (Const := Const) .prop p q = (p \ q) ⊔ (q \ p) :=
  by simp [RepEqv]

@[simp] theorem repEqv_base
    {b : Base}
    {x y : ClosedTerm (HInf Base Const) (.base b)} :
    RepEqv (Base := Base) (Const := Const) (.base b) x y =
      representedBaseEq (Base := Base) (Const := Const) b x y :=
  by simp [RepEqv]

@[simp] theorem repEqv_arr
    {σ τ : Ty Base}
    {f g : RepresentedCarrier Base Const (σ ⇒ τ)} :
    RepEqv (Base := Base) (Const := Const) (σ ⇒ τ) f g =
      sSup
        (Set.range
          (fun x : {x : RepresentedCarrier Base Const σ //
              Admissible (Base := Base) (Const := Const) σ x} =>
            RepEqv (Base := Base) (Const := Const) τ (f x.1) (g x.1))) :=
  by simp [RepEqv]

theorem repEqv_symm :
    ∀ {τ : Ty Base}
      {x y : RepresentedCarrier Base Const τ},
      RepEqv (Base := Base) (Const := Const) τ x y =
        RepEqv (Base := Base) (Const := Const) τ y x
  | .prop, x, y => by
      rw [repEqv_prop, repEqv_prop, sup_comm]
  | .base b, x, y => by
      simpa [RepEqv] using
        representedBaseEq_symm (Base := Base) (Const := Const) (b := b) x y
  | .arr σ τ, f, g => by
      have hRange :
          Set.range
              (fun x : {x : RepresentedCarrier Base Const σ //
                  Admissible (Base := Base) (Const := Const) σ x} =>
                RepEqv (Base := Base) (Const := Const) τ (f x.1) (g x.1)) =
            Set.range
              (fun x : {x : RepresentedCarrier Base Const σ //
                  Admissible (Base := Base) (Const := Const) σ x} =>
                RepEqv (Base := Base) (Const := Const) τ (g x.1) (f x.1)) := by
        ext a
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, by simpa using
            (repEqv_symm (τ := τ) (x := f x.1) (y := g x.1)).symm⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x, by simpa using
            (repEqv_symm (τ := τ) (x := f x.1) (y := g x.1))⟩
      rw [repEqv_arr, repEqv_arr, hRange]

@[simp] theorem henkinTruthSet_top_eq_bot :
    henkinTruthSet (Base := Base) (Const := Const) (.top : ClosedFormula (HInf Base Const)) =
      (⊥ : HenkinTruthVal Base Const) := by
  ext W
  constructor
  · intro _h
    simp
  · intro _h
    simpa [henkinTruthSet] using W.1.top_mem

@[simp] theorem henkinTruthSet_bot_eq_top :
    henkinTruthSet (Base := Base) (Const := Const) (.bot : ClosedFormula (HInf Base Const)) =
      (⊤ : HenkinTruthVal Base Const) := by
  ext W
  constructor
  · intro h
    exact False.elim (W.1.bot_not_mem ((mem_henkinTruthSet_iff
      (Base := Base) (Const := Const) (W := W)).1 h))
  · intro h
    cases h

@[simp] theorem henkinTruthSet_and_eq_sup
    {p q : ClosedFormula (HInf Base Const)} :
    henkinTruthSet (Base := Base) (Const := Const) (.and p q) =
      henkinTruthSet (Base := Base) (Const := Const) p ⊔
        henkinTruthSet (Base := Base) (Const := Const) q := by
  ext W
  change
    W ∈ henkinTruthSet (Base := Base) (Const := Const) (.and p q) ↔
      W ∈ henkinTruthSet (Base := Base) (Const := Const) p ⊔
        henkinTruthSet (Base := Base) (Const := Const) q
  rw [UpperSet.mem_sup_iff]
  simpa [henkinTruthSet] using
    (ClosedTheorySet.World.mem_truthSet_and_iff
      (Const := HInf Base Const)
      (W := W.1)
      (φ := p)
      (ψ := q))

@[simp] theorem henkinTruthSet_or_eq_inf
    {p q : ClosedFormula (HInf Base Const)} :
    henkinTruthSet (Base := Base) (Const := Const) (.or p q) =
      henkinTruthSet (Base := Base) (Const := Const) p ⊓
        henkinTruthSet (Base := Base) (Const := Const) q := by
  ext W
  change
    W ∈ henkinTruthSet (Base := Base) (Const := Const) (.or p q) ↔
      W ∈ henkinTruthSet (Base := Base) (Const := Const) p ⊓
        henkinTruthSet (Base := Base) (Const := Const) q
  rw [UpperSet.mem_inf_iff]
  simpa [henkinTruthSet] using
    (ClosedTheorySet.World.mem_truthSet_or_iff
      (Const := HInf Base Const)
      (W := W.1)
      (φ := p)
      (ψ := q))

theorem henkinTruthSet_imp_le_iff
    {p q : ClosedFormula (HInf Base Const)}
    {s : HenkinTruthVal Base Const} :
    henkinTruthSet (Base := Base) (Const := Const) (.imp p q) ≤ s ↔
      henkinTruthSet (Base := Base) (Const := Const) q ≤
        henkinTruthSet (Base := Base) (Const := Const) p ⊔ s := by
  constructor
  · intro h
    intro W hW
    change W ∈ henkinTruthSet (Base := Base) (Const := Const) p ⊔ s at hW
    change W ∈ henkinTruthSet (Base := Base) (Const := Const) q
    rw [UpperSet.mem_sup_iff] at hW
    rcases hW with ⟨hpW, hsW⟩
    have hImpW :
        W ∈ henkinTruthSet (Base := Base) (Const := Const) (.imp p q) :=
      h hsW
    exact
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2 <|
        W.1.mp
          ((mem_henkinTruthSet_iff
            (Base := Base)
            (Const := Const)
            (W := W)).1 hImpW)
          ((mem_henkinTruthSet_iff
            (Base := Base)
            (Const := Const)
            (W := W)).1 hpW)
  · intro h
    intro W hsW
    change W ∈ henkinTruthSet (Base := Base) (Const := Const) (.imp p q)
    apply
      (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
    have hForces :
        ClosedTheorySet.World.ForcesImp (Const := HInf Base Const) W.1 p q := by
      intro V hWV hpV
      let Vh : HenkinWorld Base Const :=
        ⟨V, by
          intro χ hχ
          exact hWV (W.2 hχ)⟩
      have hsV : Vh ∈ s :=
        s.upper hWV hsW
      have hpsV :
          Vh ∈ henkinTruthSet (Base := Base) (Const := Const) p ⊔ s := by
        rw [UpperSet.mem_sup_iff]
        exact
          ⟨(mem_henkinTruthSet_iff
              (Base := Base)
              (Const := Const)
              (W := Vh)).2 hpV,
            hsV⟩
      exact
        (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := Vh)).1
          (h hpsV)
    exact
      (forcesImp_iff_mem
        (Base := Base)
        (Const := Const)
        (W := W.1)
        W.2
        (φ := p)
        (ψ := q)).1 hForces

@[simp] theorem henkinTruthSet_imp_eq_sdiff
    {p q : ClosedFormula (HInf Base Const)} :
    henkinTruthSet (Base := Base) (Const := Const) (.imp p q) =
      henkinTruthSet (Base := Base) (Const := Const) q \
        henkinTruthSet (Base := Base) (Const := Const) p := by
  apply le_antisymm
  · rw [henkinTruthSet_imp_le_iff]
    exact le_sup_sdiff
  · rw [sdiff_le_iff]
    exact
      (henkinTruthSet_imp_le_iff
        (Base := Base)
        (Const := Const)
        (p := p)
        (q := q)
        (s := henkinTruthSet (Base := Base) (Const := Const) (.imp p q))).1
        le_rfl

@[simp] theorem henkinTruthSet_not_eq_sdiff
    {p : ClosedFormula (HInf Base Const)} :
    henkinTruthSet (Base := Base) (Const := Const) (.not p) =
      (((⊤ : HenkinTruthVal Base Const) \
          henkinTruthSet (Base := Base) (Const := Const) p) :
        HenkinTruthVal Base Const) := by
  calc
    henkinTruthSet (Base := Base) (Const := Const) (.not p) =
        henkinTruthSet (Base := Base) (Const := Const)
          (.imp p (.bot : ClosedFormula (HInf Base Const))) := by
          ext W
          constructor
          · intro hNot
            apply (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
            apply (forcesImp_iff_mem (Base := Base) (Const := Const) (W := W.1) W.2).1
            intro V hWV hpV
            exact False.elim
              ((forcesNot_iff_mem (Base := Base) (Const := Const) (W := W.1) W.2).2
                hNot hWV hpV)
          · intro hImp
            apply (mem_henkinTruthSet_iff (Base := Base) (Const := Const) (W := W)).2
            apply (forcesNot_iff_mem (Base := Base) (Const := Const) (W := W.1) W.2).1
            intro V hWV hpV
            exact
              V.bot_not_mem
                ((forcesImp_iff_mem (Base := Base) (Const := Const) (W := W.1) W.2).2
                  hImp hWV hpV)
    _ =
        (henkinTruthSet (Base := Base) (Const := Const)
            (.bot : ClosedFormula (HInf Base Const)) \
          henkinTruthSet (Base := Base) (Const := Const) p :
            HenkinTruthVal Base Const) := by
          simpa using
            (henkinTruthSet_imp_eq_sdiff (Base := Base) (Const := Const)
              (p := p) (q := (.bot : ClosedFormula (HInf Base Const))))
    _ =
        (((⊤ : HenkinTruthVal Base Const) \
            henkinTruthSet (Base := Base) (Const := Const) p) :
          HenkinTruthVal Base Const) := by
          simp

/-- Proposition extensionality identifies proposition equality with the
conjunction of the two implication directions. -/
theorem henkinProvable_eq_prop_biimp_formula
    {p q : ClosedFormula (HInf Base Const)} :
    HenkinProvable (Base := Base) (Const := Const)
      (.eq (.eq p q) (.and (.imp p q) (.imp q p))) := by
  exact
    henkinProvable_of_theorem (Base := Base) (Const := Const) <|
      ExtDerivation.eqPropI
        (ExtDerivation.impI <|
          ExtDerivation.andI
            (ExtDerivation.eqPropEL
              (ExtDerivation.hyp
                (Δ := [.eq p q])
                (φ := (.eq p q : ClosedFormula (HInf Base Const)))
                (by simp)))
            (ExtDerivation.eqPropER
              (ExtDerivation.hyp
                (Δ := [.eq p q])
                (φ := (.eq p q : ClosedFormula (HInf Base Const)))
                (by simp))))
        (ExtDerivation.impI <|
          ExtDerivation.eqPropI
            (ExtDerivation.andEL
              (ExtDerivation.hyp
                (Δ := [.and (.imp p q) (.imp q p)])
                (φ := (.and (.imp p q) (.imp q p) : ClosedFormula (HInf Base Const)))
                (by simp)))
            (ExtDerivation.andER
              (ExtDerivation.hyp
                (Δ := [.and (.imp p q) (.imp q p)])
                (φ := (.and (.imp p q) (.imp q p) : ClosedFormula (HInf Base Const)))
                (by simp))))

/-- Proposition-type equality formulas represent the transported proposition
equality object on represented truth values. -/
theorem represents_eq_formula_prop
    {p q : ClosedFormula (HInf Base Const)}
    {x y : RepresentedCarrier Base Const .prop}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hq : Represents (Base := Base) (Const := Const) .prop q y) :
    Represents (Base := Base) (Const := Const) .prop (.eq p q)
      (RepEqv (Base := Base) (Const := Const) .prop x y) := by
  have hBiimp :
      Represents (Base := Base) (Const := Const) .prop
        (.and (.imp p q) (.imp q p))
        (RepEqv (Base := Base) (Const := Const) .prop x y) := by
    rw [represents_prop_iff, repEqv_prop]
    rw [← (represents_prop_iff (Base := Base) (Const := Const)).1 hp]
    rw [← (represents_prop_iff (Base := Base) (Const := Const)).1 hq]
    rw [henkinTruthSet_and_eq_sup, henkinTruthSet_imp_eq_sdiff, henkinTruthSet_imp_eq_sdiff]
    rw [sup_comm]
  exact
    represents_prop_of_henkinProvable_eq
      (Base := Base)
      (Const := Const)
      hBiimp
      (henkinProvable_eq_symm
        (Base := Base)
        (Const := Const)
        henkinProvable_eq_prop_biimp_formula)

/--
Closed Henkin-provable equalities of base representatives induce propositional
equality of their base-equality formulas.

Positive example:
- if `t = x` and `u = y` are Henkin-provable, then the formulas `t = u` and
  `x = y` are propositionally equal modulo the Henkin axioms.

Negative example:
- this is only the base-type branch; the corresponding function-type step is
  the genuinely harder extensional theorem.
-/
theorem henkinProvable_eq_base_formula
    {b : Base}
    {t u x y : ClosedTerm (HInf Base Const) (.base b)}
    (htx : HenkinProvable (Base := Base) (Const := Const) (.eq t x))
    (huy : HenkinProvable (Base := Base) (Const := Const) (.eq u y)) :
    HenkinProvable (Base := Base) (Const := Const)
      (.eq (.eq t u) (.eq x y)) := by
  rcases htx with ⟨Γ₁, hΓ₁, htx⟩
  rcases huy with ⟨Γ₂, hΓ₂, huy⟩
  have hForward :
      HenkinProvable (Base := Base) (Const := Const)
        (.imp (.eq t u) (.eq x y)) := by
    refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
    · intro ψ hψ
      rcases List.mem_append.mp hψ with hψ | hψ
      · exact hΓ₁ ψ hψ
      · exact hΓ₂ ψ hψ
    · apply ExtDerivation.impI
      have htu' :
          ExtDerivation (HInf Base Const)
            ((.eq t u : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq t u) :=
        .hyp (by simp)
      have htx' :
          ExtDerivation (HInf Base Const)
            ((.eq t u : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq t x) := by
        exact
          ExtDerivation.mono
            (by
              intro ψ hψ
              simp [List.mem_append, hψ])
            htx
      have huy' :
          ExtDerivation (HInf Base Const)
            ((.eq t u : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq u y) := by
        exact
          ExtDerivation.mono
            (by
              intro ψ hψ
              simp [List.mem_append, hψ])
            huy
      have hxt' :
          ExtDerivation (HInf Base Const)
            ((.eq t u : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq x t) :=
        ExtDerivation.eqSymm htx'
      have hxu' :
          ExtDerivation (HInf Base Const)
            ((.eq t u : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq x u) :=
        ExtDerivation.eqTrans hxt' htu'
      exact ExtDerivation.eqTrans hxu' huy'
  have hBackward :
      HenkinProvable (Base := Base) (Const := Const)
        (.imp (.eq x y) (.eq t u)) := by
    refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
    · intro ψ hψ
      rcases List.mem_append.mp hψ with hψ | hψ
      · exact hΓ₁ ψ hψ
      · exact hΓ₂ ψ hψ
    · apply ExtDerivation.impI
      have hxy' :
          ExtDerivation (HInf Base Const)
            ((.eq x y : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq x y) :=
        .hyp (by simp)
      have htx' :
          ExtDerivation (HInf Base Const)
            ((.eq x y : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq t x) := by
        exact
          ExtDerivation.mono
            (by
              intro ψ hψ
              simp [List.mem_append, hψ])
            htx
      have huy' :
          ExtDerivation (HInf Base Const)
            ((.eq x y : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq u y) := by
        exact
          ExtDerivation.mono
            (by
              intro ψ hψ
              simp [List.mem_append, hψ])
            huy
      have hyu' :
          ExtDerivation (HInf Base Const)
            ((.eq x y : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq y u) :=
        ExtDerivation.eqSymm huy'
      have hty' :
          ExtDerivation (HInf Base Const)
            ((.eq x y : ClosedFormula (HInf Base Const)) :: (Γ₁ ++ Γ₂))
            (.eq t y) :=
        ExtDerivation.eqTrans htx' hxy'
      exact ExtDerivation.eqTrans hty' hyu'
  rcases hForward with ⟨Γf, hΓf, hForward⟩
  rcases hBackward with ⟨Γb, hΓb, hBackward⟩
  refine ⟨Γf ++ Γb, ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hΓf ψ hψ
    · exact hΓb ψ hψ
  · exact
      ExtDerivation.eqPropI
        (ExtDerivation.mono
          (by
            intro ψ hψ
            exact List.mem_append_left _ hψ)
          hForward)
        (ExtDerivation.mono
          (by
            intro ψ hψ
            exact List.mem_append_right _ hψ)
          hBackward)

/-- Base-type equality formulas represent the semantic base equality relation. -/
theorem represents_eq_formula_base
    {b : Base}
    {t u x y : ClosedTerm (HInf Base Const) (.base b)}
    (ht : Represents (Base := Base) (Const := Const) (.base b) t x)
    (hu : Represents (Base := Base) (Const := Const) (.base b) u y) :
    Represents (Base := Base) (Const := Const) .prop (.eq t u)
      (RepEqv (Base := Base) (Const := Const) (.base b) x y) := by
  have hRepXY :
      Represents (Base := Base) (Const := Const) .prop (.eq x y)
        (RepEqv (Base := Base) (Const := Const) (.base b) x y) := by
    rw [represents_prop_iff, repEqv_base, representedBaseEq]
  have hEqXY_TU :
      HenkinProvable (Base := Base) (Const := Const)
        (.eq (.eq x y) (.eq t u)) :=
    henkinProvable_eq_symm
      (Base := Base)
      (Const := Const)
      (henkinProvable_eq_base_formula
        (Base := Base)
        (Const := Const)
        (b := b)
        (by simpa [represents_base_iff] using ht)
        (by simpa [represents_base_iff] using hu))
  exact
    represents_prop_of_henkinProvable_eq
      (Base := Base)
      (Const := Const)
      hRepXY
      hEqXY_TU

@[simp] theorem represents_top_formula :
    Represents (Base := Base) (Const := Const) .prop
      (.top : ClosedFormula (HInf Base Const))
      (⊥ : HenkinTruthVal Base Const) := by
  rw [represents_prop_iff]
  exact henkinTruthSet_top_eq_bot (Base := Base) (Const := Const)

@[simp] theorem represents_bot_formula :
    Represents (Base := Base) (Const := Const) .prop
      (.bot : ClosedFormula (HInf Base Const))
      (⊤ : HenkinTruthVal Base Const) := by
  rw [represents_prop_iff]
  exact henkinTruthSet_bot_eq_top (Base := Base) (Const := Const)

theorem represents_and_formula
    {p q : ClosedFormula (HInf Base Const)}
    {x y : HenkinTruthVal Base Const}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hq : Represents (Base := Base) (Const := Const) .prop q y) :
    Represents (Base := Base) (Const := Const) .prop (.and p q)
      ((x ⊔ y : HenkinTruthVal Base Const)) := by
  rw [represents_prop_iff] at hp hq ⊢
  rw [henkinTruthSet_and_eq_sup, hp, hq]

theorem represents_or_formula
    {p q : ClosedFormula (HInf Base Const)}
    {x y : HenkinTruthVal Base Const}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hq : Represents (Base := Base) (Const := Const) .prop q y) :
    Represents (Base := Base) (Const := Const) .prop (.or p q)
      ((x ⊓ y : HenkinTruthVal Base Const)) := by
  rw [represents_prop_iff] at hp hq ⊢
  rw [henkinTruthSet_or_eq_inf, hp, hq]

theorem represents_imp_formula
    {p q : ClosedFormula (HInf Base Const)}
    {x y : HenkinTruthVal Base Const}
    (hp : Represents (Base := Base) (Const := Const) .prop p x)
    (hq : Represents (Base := Base) (Const := Const) .prop q y) :
    Represents (Base := Base) (Const := Const) .prop (.imp p q)
      ((y \ x : HenkinTruthVal Base Const)) := by
  rw [represents_prop_iff] at hp hq ⊢
  rw [henkinTruthSet_imp_eq_sdiff, hp, hq]

theorem represents_not_formula
    {p : ClosedFormula (HInf Base Const)}
    {x : HenkinTruthVal Base Const}
    (hp : Represents (Base := Base) (Const := Const) .prop p x) :
    Represents (Base := Base) (Const := Const) .prop (.not p)
      (((⊤ : HenkinTruthVal Base Const) \ x : HenkinTruthVal Base Const)) := by
  rw [represents_prop_iff] at hp ⊢
  rw [henkinTruthSet_not_eq_sdiff, hp]

/--
Universe-stable proposition object for the represented canonical bridge.

This packages the raw Henkin-world truth values into the size expected by the
standard `HeytingPreModel` interface while keeping the order dual explicit.
-/
abbrev LiftedHenkinTruthVal (Base : Type u) (Const : Ty Base → Type v) :
    Type (max (u + 1) (v + 1)) :=
  ULift.{max (u + 1) (v + 1), max u (v + 1)}
    (OrderDual (HenkinTruthVal Base Const))

noncomputable instance instHeytingAlgebraLiftedHenkinTruthVal :
    HeytingAlgebra (LiftedHenkinTruthVal Base Const) where
  toGeneralizedHeytingAlgebra :=
    { __ := (inferInstance : Lattice (LiftedHenkinTruthVal Base Const))
      __ := (inferInstance : OrderTop (LiftedHenkinTruthVal Base Const))
      himp := fun a b => ULift.up (a.down ⇨ b.down)
      le_himp_iff := by
        intro a b c
        change a.down ≤ b.down ⇨ c.down ↔ a.down ⊓ b.down ≤ c.down
        exact le_himp_iff }
  __ := (inferInstance : OrderBot (LiftedHenkinTruthVal Base Const))
  compl := fun a => ULift.up (a.downᶜ)
  himp_bot := by
    intro a
    apply ULift.ext
    exact himp_bot a.down

noncomputable instance instFrameLiftedHenkinTruthVal :
    Order.Frame (LiftedHenkinTruthVal Base Const) := by
  exact
    { __ := (inferInstance : CompleteLattice (LiftedHenkinTruthVal Base Const))
      __ := (inferInstance : HeytingAlgebra (LiftedHenkinTruthVal Base Const)) }

/-- Universe-stable base carrier for the represented canonical bridge. -/
abbrev LiftedHenkinBaseCarrier
    (Base : Type u) (Const : Ty Base → Type v) (b : Base) :
    Type (max (u + 1) (v + 1)) :=
  ULift.{max (u + 1) (v + 1), max u (v + 1)}
    (ClosedTerm (HInf Base Const) (.base b))

/--
Universe-stable semantic carrier family for the represented canonical bridge.

This is intentionally separate from `RepresentedCarrier`: it is the staging
layer for the future `HeytingPreModel` package, not a replacement for the raw
represented semantics.
-/
def LiftedRepresentedCarrier (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max (u + 1) (v + 1))
  | .prop => LiftedHenkinTruthVal Base Const
  | .base b => LiftedHenkinBaseCarrier Base Const b
  | .arr σ τ => LiftedRepresentedCarrier Base Const σ → LiftedRepresentedCarrier Base Const τ

/-- Type-by-type equivalence between the raw and universe-stable represented layers. -/
def representedEquiv :
    (τ : Ty Base) →
      RepresentedCarrier Base Const τ ≃ LiftedRepresentedCarrier Base Const τ
  | .prop =>
      { toFun := fun p =>
          (ULift.up
            (show OrderDual (HenkinTruthVal Base Const) from p) :
              LiftedHenkinTruthVal Base Const)
        invFun := fun p =>
          show HenkinTruthVal Base Const from
            (p.down : OrderDual (HenkinTruthVal Base Const))
        left_inv := by intro p; rfl
        right_inv := by intro p; cases p; rfl }
  | .base b =>
      { toFun := fun t =>
          (ULift.up t : LiftedHenkinBaseCarrier Base Const b)
        invFun := fun t => (t.down : ClosedTerm (HInf Base Const) (.base b))
        left_inv := by intro t; rfl
        right_inv := by intro t; cases t; rfl }
  | .arr σ τ =>
      let eσ := representedEquiv σ
      let eτ := representedEquiv τ
      { toFun := fun f x => eτ (f (eσ.symm x))
        invFun := fun f x => eτ.symm (f (eσ x))
        left_inv := by
          intro f
          funext x
          simp
        right_inv := by
          intro f
          funext x
          simp }
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

abbrev liftRepresented
    (τ : Ty Base) :
    RepresentedCarrier Base Const τ →
      LiftedRepresentedCarrier Base Const τ :=
  (representedEquiv (Base := Base) (Const := Const) τ).toFun

/-- Lower a universe-stable represented value back to the raw represented layer. -/
abbrev lowerLiftedRepresented
    (τ : Ty Base) :
    LiftedRepresentedCarrier Base Const τ →
      RepresentedCarrier Base Const τ :=
  (representedEquiv (Base := Base) (Const := Const) τ).invFun

@[simp] theorem lowerLiftedRepresented_liftRepresented :
    ∀ (τ : Ty Base) (x : RepresentedCarrier Base Const τ),
      lowerLiftedRepresented (Base := Base) (Const := Const) τ
          (liftRepresented (Base := Base) (Const := Const) τ x) = x
  | τ, x => (representedEquiv (Base := Base) (Const := Const) τ).left_inv x

@[simp] theorem liftRepresented_lowerLiftedRepresented :
    ∀ (τ : Ty Base) (x : LiftedRepresentedCarrier Base Const τ),
      liftRepresented (Base := Base) (Const := Const) τ
          (lowerLiftedRepresented (Base := Base) (Const := Const) τ x) = x
  | τ, x => (representedEquiv (Base := Base) (Const := Const) τ).right_inv x

/-- Admissibility transported to the universe-stable represented layer. -/
def LiftedAdmissible
    (τ : Ty Base) (x : LiftedRepresentedCarrier Base Const τ) : Prop :=
  Admissible (Base := Base) (Const := Const) τ
    (lowerLiftedRepresented (Base := Base) (Const := Const) τ x)

@[simp] theorem liftedAdmissible_liftRepresented_iff
    {τ : Ty Base}
    {x : RepresentedCarrier Base Const τ} :
    LiftedAdmissible (Base := Base) (Const := Const) τ
        (liftRepresented (Base := Base) (Const := Const) τ x) ↔
      Admissible (Base := Base) (Const := Const) τ x := by
  simp [LiftedAdmissible]

/-- Constant interpretation data transported to the universe-stable layer. -/
structure LiftedRepresentedConstDenotation
    (Base : Type u) (Const : Ty Base → Type v) where
  val :
    {τ : Ty Base} →
      HInf Base Const τ →
        LiftedRepresentedCarrier Base Const τ
  spec :
    ∀ {τ : Ty Base} (c : HInf Base Const τ),
      Represents (Base := Base) (Const := Const) τ (.const c)
        (lowerLiftedRepresented (Base := Base) (Const := Const) τ (val c))

/-- Lift raw represented constant data to the universe-stable layer. -/
def RepresentedConstDenotation.toLifted
    (D : RepresentedConstDenotation Base Const) :
    LiftedRepresentedConstDenotation Base Const where
  val := fun {τ} c => liftRepresented (Base := Base) (Const := Const) τ (D.val c)
  spec := by
    intro τ c
    simpa using D.spec c

/--
Recursive equivalence from the standard `Ty.denoteHeyting` interpretation over
the lifted leaves to the staged represented semantics.
-/
def liftedHeytingEquiv :
    (τ : Ty Base) →
      Ty.denoteHeyting
          (LiftedHenkinBaseCarrier Base Const)
          (LiftedHenkinTruthVal Base Const)
          τ ≃
        LiftedRepresentedCarrier Base Const τ
  | .prop =>
      Equiv.refl _
  | .base _ =>
      Equiv.refl _
  | .arr σ τ =>
      let eσ := liftedHeytingEquiv σ
      let eτ := liftedHeytingEquiv τ
      { toFun := fun f x => eτ (f (eσ.symm x))
        invFun := fun f x => eτ.symm (f (eσ x))
        left_inv := by
          intro f
          funext x
          simp
        right_inv := by
          intro f
          funext x
          simp }
termination_by τ => sizeOf τ
decreasing_by
  all_goals
    simp_wf
    try omega

abbrev fromLiftedHeyting
    (τ : Ty Base) :
    Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        τ →
      LiftedRepresentedCarrier Base Const τ :=
  (liftedHeytingEquiv (Base := Base) (Const := Const) τ).toFun

abbrev toLiftedHeyting
    (τ : Ty Base) :
    LiftedRepresentedCarrier Base Const τ →
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        τ :=
  (liftedHeytingEquiv (Base := Base) (Const := Const) τ).invFun

@[simp] theorem fromLiftedHeyting_toLiftedHeyting
    (τ : Ty Base)
    (x : LiftedRepresentedCarrier Base Const τ) :
    fromLiftedHeyting (Base := Base) (Const := Const) τ
        (toLiftedHeyting (Base := Base) (Const := Const) τ x) = x :=
  (liftedHeytingEquiv (Base := Base) (Const := Const) τ).right_inv x

@[simp] theorem toLiftedHeyting_fromLiftedHeyting
    (τ : Ty Base)
    (x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        τ) :
    toLiftedHeyting (Base := Base) (Const := Const) τ
        (fromLiftedHeyting (Base := Base) (Const := Const) τ x) = x :=
  (liftedHeytingEquiv (Base := Base) (Const := Const) τ).left_inv x

/-- Admissibility on the standard `Ty.denoteHeyting` interpretation, transported
through the lifted represented staging layer. -/
def LiftedHeytingAdmissible
    (τ : Ty Base)
    (x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        τ) : Prop :=
  LiftedAdmissible (Base := Base) (Const := Const) τ
    (fromLiftedHeyting (Base := Base) (Const := Const) τ x)

@[simp] theorem liftedHeytingAdmissible_toLiftedHeyting_iff
    {τ : Ty Base}
    {x : LiftedRepresentedCarrier Base Const τ} :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) τ
        (toLiftedHeyting (Base := Base) (Const := Const) τ x) ↔
      LiftedAdmissible (Base := Base) (Const := Const) τ x := by
  simp [LiftedHeytingAdmissible]

@[simp] theorem lowerLiftedRepresented_app
    {σ τ : Ty Base}
    (f : LiftedRepresentedCarrier Base Const (σ ⇒ τ))
    (x : LiftedRepresentedCarrier Base Const σ) :
    lowerLiftedRepresented (Base := Base) (Const := Const) (σ ⇒ τ) f
        (lowerLiftedRepresented (Base := Base) (Const := Const) σ x) =
      lowerLiftedRepresented (Base := Base) (Const := Const) τ (f x) := by
  simp [lowerLiftedRepresented, representedEquiv]

@[simp] theorem fromLiftedHeyting_app
    {σ τ : Ty Base}
    (f :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        (σ ⇒ τ))
    (x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        σ) :
    fromLiftedHeyting (Base := Base) (Const := Const) (σ ⇒ τ) f
        (fromLiftedHeyting (Base := Base) (Const := Const) σ x) =
      fromLiftedHeyting (Base := Base) (Const := Const) τ (f x) := by
  simp [fromLiftedHeyting, liftedHeytingEquiv]

theorem liftedAdmissible_app
    {σ τ : Ty Base}
    {f : LiftedRepresentedCarrier Base Const (σ ⇒ τ)}
    {x : LiftedRepresentedCarrier Base Const σ}
    (hf : LiftedAdmissible (Base := Base) (Const := Const) (σ ⇒ τ) f)
    (hx : LiftedAdmissible (Base := Base) (Const := Const) σ x) :
    LiftedAdmissible (Base := Base) (Const := Const) τ (f x) := by
  unfold LiftedAdmissible at hf hx ⊢
  have happ :=
    lowerLiftedRepresented_app
      (Base := Base)
      (Const := Const)
      (σ := σ)
      (τ := τ)
      f x
  rw [← happ]
  exact admissible_app (Base := Base) (Const := Const) hf hx

theorem liftedHeytingAdmissible_app
    {σ τ : Ty Base}
    {f :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        (σ ⇒ τ)}
    {x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        σ}
    (hf : LiftedHeytingAdmissible (Base := Base) (Const := Const) (σ ⇒ τ) f)
    (hx : LiftedHeytingAdmissible (Base := Base) (Const := Const) σ x) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) τ (f x) := by
  unfold LiftedHeytingAdmissible at hf hx ⊢
  rw [← fromLiftedHeyting_app]
  exact liftedAdmissible_app (Base := Base) (Const := Const) hf hx

theorem liftedHeytingAdmissible_of_represents
    {τ : Ty Base}
    {x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        τ}
    {t : ClosedTerm (HInf Base Const) τ}
    (ht : Represents (Base := Base) (Const := Const) τ t
      (lowerLiftedRepresented (Base := Base) (Const := Const) τ
        (fromLiftedHeyting (Base := Base) (Const := Const) τ x))) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) τ x := by
  exact ⟨t, ht⟩

theorem liftedHeytingAdmissible_truthSet
    (φ : ClosedFormula (HInf Base Const)) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) .prop
      (toLiftedHeyting
        (Base := Base)
        (Const := Const)
        .prop
        (liftRepresented
          (Base := Base)
          (Const := Const)
          .prop
          (show HenkinTruthVal Base Const from
            henkinTruthSet (Base := Base) (Const := Const) φ))) := by
  simpa [LiftedHeytingAdmissible, LiftedAdmissible] using
    ((liftedAdmissible_liftRepresented_iff
      (Base := Base)
      (Const := Const)
      (τ := .prop)
      (x := (show RepresentedCarrier Base Const .prop from
        henkinTruthSet (Base := Base) (Const := Const) φ))).2
      (admissible_truthSet (Base := Base) (Const := Const) φ))

theorem liftedHeytingAdmissible_base
    {b : Base}
    (t : LiftedHenkinBaseCarrier Base Const b) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) (.base b)
      (toLiftedHeyting (Base := Base) (Const := Const) (.base b) t) := by
  rw [liftedHeytingAdmissible_toLiftedHeyting_iff]
  cases t with
  | up u =>
      simpa [LiftedAdmissible, lowerLiftedRepresented, representedEquiv] using
        (admissible_base (Base := Base) (Const := Const) u)

theorem liftedHeytingAdmissible_base_self
    {b : Base}
    (t : LiftedHenkinBaseCarrier Base Const b) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) (.base b) t := by
  cases t with
  | up u =>
      simpa [LiftedHeytingAdmissible, fromLiftedHeyting, LiftedAdmissible,
        lowerLiftedRepresented, liftedHeytingEquiv, representedEquiv] using
        (admissible_base (Base := Base) (Const := Const) u)

/-- Valuations into the lifted standard `Ty.denoteHeyting` staging layer. -/
abbrev LiftedHeytingValuation
    (Base : Type u) (Const : Ty Base → Type v) (Γ : Ctx Base) :=
  ∀ {τ : Ty Base}, Var Γ τ →
    Ty.denoteHeyting
      (LiftedHenkinBaseCarrier Base Const)
      (LiftedHenkinTruthVal Base Const)
      τ

/-- Lower a lifted staged valuation back to the raw represented valuation layer. -/
def lowerLiftedHeytingValuation
    {Γ : Ctx Base}
    (ρ : LiftedHeytingValuation Base Const Γ) :
    Valuation (Base := Base) (Const := Const) Γ :=
  fun {_τ} v =>
    lowerLiftedRepresented
      (Base := Base)
      (Const := Const)
      _τ
      (fromLiftedHeyting
        (Base := Base)
        (Const := Const)
        _τ
        (ρ v))

theorem valuationAdmissible_lowerLiftedHeytingValuation
    {Γ : Ctx Base}
    {ρ : LiftedHeytingValuation Base Const Γ}
    (hρ :
      ∀ {τ : Ty Base} (v : Var Γ τ),
        LiftedHeytingAdmissible (Base := Base) (Const := Const) τ (ρ v)) :
    ValuationAdmissible
      (Base := Base)
      (Const := Const)
      (lowerLiftedHeytingValuation (Base := Base) (Const := Const) ρ) := by
  intro τ v
  simpa [lowerLiftedHeytingValuation, LiftedHeytingAdmissible] using hρ v

/-- Choose a closed Henkin code for each variable of an admissible lifted staged valuation. -/
noncomputable def chooseLiftedClosedSubst
    {Γ : Ctx Base}
    (ρ : LiftedHeytingValuation Base Const Γ) :
    ClosedSubst Base Const Γ :=
  fun {_τ} v =>
    chooseCode
      (Base := Base)
      (Const := Const)
      (lowerLiftedHeytingValuation
        (Base := Base)
        (Const := Const)
        ρ
        v)

theorem substRep_chooseLiftedClosedSubst
    {Γ : Ctx Base}
    {ρ : LiftedHeytingValuation Base Const Γ}
    (hρ :
      ∀ {τ : Ty Base} (v : Var Γ τ),
        LiftedHeytingAdmissible (Base := Base) (Const := Const) τ (ρ v)) :
    SubstRep
      (Base := Base)
      (Const := Const)
      (chooseLiftedClosedSubst (Base := Base) (Const := Const) ρ)
      (lowerLiftedHeytingValuation (Base := Base) (Const := Const) ρ) := by
  intro τ v
  exact
    chooseCode_represents
      (Base := Base)
      (Const := Const)
      (valuationAdmissible_lowerLiftedHeytingValuation
        (Base := Base)
        (Const := Const)
        (ρ := ρ)
        hρ
        v)

/-- Transport lifted represented constant data to the standard
`Ty.denoteHeyting` interpretation over the lifted leaves. -/
def LiftedRepresentedConstDenotation.toLiftedHeyting
    (D : LiftedRepresentedConstDenotation Base Const) :
    {τ : Ty Base} →
      HInf Base Const τ →
        Ty.denoteHeyting
          (LiftedHenkinBaseCarrier Base Const)
          (LiftedHenkinTruthVal Base Const)
          τ :=
  fun {τ} c =>
    HenkinConstInfinity.toLiftedHeyting (Base := Base) (Const := Const) τ (D.val c)

theorem LiftedRepresentedConstDenotation.toLiftedHeyting_spec
    (D : LiftedRepresentedConstDenotation Base Const)
    {τ : Ty Base}
    (c : HInf Base Const τ) :
    Represents (Base := Base) (Const := Const) τ (.const c)
      (lowerLiftedRepresented (Base := Base) (Const := Const) τ
        (fromLiftedHeyting (Base := Base) (Const := Const) τ
          (D.toLiftedHeyting c))) := by
  simpa [LiftedRepresentedConstDenotation.toLiftedHeyting] using D.spec c

theorem LiftedRepresentedConstDenotation.toLiftedHeyting_mem
    (D : LiftedRepresentedConstDenotation Base Const)
    {τ : Ty Base}
    (c : HInf Base Const τ) :
    LiftedHeytingAdmissible (Base := Base) (Const := Const) τ
      (D.toLiftedHeyting c) := by
  exact
    liftedHeytingAdmissible_of_represents
      (Base := Base)
      (Const := Const)
      (D.toLiftedHeyting_spec c)

/-- Base-type equality transported to the lifted `HeytingPreModel` carrier. -/
def liftedRepresentedBaseEq
    (b : Base)
    (x y : LiftedHenkinBaseCarrier Base Const b) :
    LiftedHenkinTruthVal Base Const :=
  ULift.up
    (show OrderDual (HenkinTruthVal Base Const) from
      representedBaseEq (Base := Base) (Const := Const) b x.down y.down)

theorem liftedRepresentedBaseEq_refl
    {b : Base}
    (x : LiftedHenkinBaseCarrier Base Const b) :
    liftedRepresentedBaseEq (Base := Base) (Const := Const) b x x = ⊤ := by
  cases x with
  | up t =>
      rw [liftedRepresentedBaseEq]
      rw [representedBaseEq_refl]
      rfl

theorem liftedRepresentedBaseEq_symm
    {b : Base}
    (x y : LiftedHenkinBaseCarrier Base Const b) :
    liftedRepresentedBaseEq (Base := Base) (Const := Const) b x y ≤
      liftedRepresentedBaseEq (Base := Base) (Const := Const) b y x := by
  cases x with
  | up tx =>
      cases y with
      | up ty =>
          simp [liftedRepresentedBaseEq, representedBaseEq_symm]

theorem liftedRepresentedBaseEq_trans
    {b : Base}
    (x y z : LiftedHenkinBaseCarrier Base Const b) :
    liftedRepresentedBaseEq (Base := Base) (Const := Const) b x y ⊓
        liftedRepresentedBaseEq (Base := Base) (Const := Const) b y z ≤
      liftedRepresentedBaseEq (Base := Base) (Const := Const) b x z := by
  cases x with
  | up tx =>
      cases y with
      | up ty =>
          cases z with
          | up tz =>
              simpa [liftedRepresentedBaseEq] using
                (representedBaseEq_trans_le
                  (Base := Base)
                  (Const := Const)
                  (b := b)
                  tx ty tz)

/-- The transported represented canonical semantics as a genuine Heyting premodel
over the cumulative Henkin signature. -/
noncomputable def liftedRepresentedPreModel
    (D : LiftedRepresentedConstDenotation Base Const) :
    HeytingPreModel Base (HInf Base Const) where
  Ω := LiftedHenkinTruthVal Base Const
  instFrame := instFrameLiftedHenkinTruthVal
  Carrier := LiftedHenkinBaseCarrier Base Const
  adm := LiftedHeytingAdmissible (Base := Base) (Const := Const)
  base_mem _ x := liftedHeytingAdmissible_base_self (Base := Base) (Const := Const) x
  app_mem hf hx :=
    liftedHeytingAdmissible_app (Base := Base) (Const := Const) hf hx
  constDen := D.toLiftedHeyting
  const_mem := by
    intro τ c
    exact D.toLiftedHeyting_mem c
  baseEq := liftedRepresentedBaseEq (Base := Base) (Const := Const)
  baseEq_refl _ x := liftedRepresentedBaseEq_refl (Base := Base) (Const := Const) x
  baseEq_symm _ x y := liftedRepresentedBaseEq_symm (Base := Base) (Const := Const) x y
  baseEq_trans _ x y z := liftedRepresentedBaseEq_trans (Base := Base) (Const := Const) x y z

@[simp] theorem lowerLiftedHeytingValuation_extend
    (D : LiftedRepresentedConstDenotation Base Const)
    {Γ : Ctx Base} {σ : Ty Base}
    (ρ : HeytingPreModel.Valuation (liftedRepresentedPreModel D) Γ)
    (x :
      Ty.denoteHeyting
        (LiftedHenkinBaseCarrier Base Const)
        (LiftedHenkinTruthVal Base Const)
        σ)
    {τ : Ty Base}
    (v : Var (σ :: Γ) τ) :
    lowerLiftedHeytingValuation
        (Base := Base)
        (Const := Const)
        (HeytingPreModel.extend (liftedRepresentedPreModel D) ρ x)
        v =
      Valuation.extend
        (Base := Base)
        (Const := Const)
        (lowerLiftedHeytingValuation (Base := Base) (Const := Const) ρ)
        (lowerLiftedRepresented
          (Base := Base)
          (Const := Const)
          σ
          (fromLiftedHeyting
            (Base := Base)
            (Const := Const)
            σ
            x))
        v := by
  cases v <;> rfl

theorem valuationAdmissible_lower_of_liftedRepresentedPreModel
    (D : LiftedRepresentedConstDenotation Base Const)
    {Γ : Ctx Base}
    {ρ : HeytingPreModel.Valuation (liftedRepresentedPreModel D) Γ}
    (hρ :
      HeytingPreModel.ValuationAdmissible
        (liftedRepresentedPreModel D)
        ρ) :
    ValuationAdmissible
      (Base := Base)
      (Const := Const)
      (lowerLiftedHeytingValuation (Base := Base) (Const := Const) ρ) := by
  exact
    valuationAdmissible_lowerLiftedHeytingValuation
      (Base := Base)
      (Const := Const)
      (ρ := ρ)
      hρ

theorem substRep_chooseLiftedClosedSubst_of_liftedRepresentedPreModel
    (D : LiftedRepresentedConstDenotation Base Const)
    {Γ : Ctx Base}
    {ρ : HeytingPreModel.Valuation (liftedRepresentedPreModel D) Γ}
    (hρ :
      HeytingPreModel.ValuationAdmissible
        (liftedRepresentedPreModel D)
        ρ) :
    SubstRep
      (Base := Base)
      (Const := Const)
      (chooseLiftedClosedSubst (Base := Base) (Const := Const) ρ)
      (lowerLiftedHeytingValuation (Base := Base) (Const := Const) ρ) := by
  exact
    substRep_chooseLiftedClosedSubst
      (Base := Base)
      (Const := Const)
      (ρ := ρ)
      hρ

end HenkinConstInfinity

end Mettapedia.Logic.HOL
