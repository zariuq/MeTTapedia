import Mettapedia.Logic.HOL.CanonicalModel
import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.HenkinizationInfinity

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
    omega

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
    omega

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

end HenkinConstInfinity

end Mettapedia.Logic.HOL
