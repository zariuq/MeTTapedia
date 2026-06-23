import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermQuotient
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModel
import Mettapedia.Logic.HOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open ClosedTermCanonicalWorldModel
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
Bridge from provable closed-term equality to semantic `PreModel.Eqv`.

The current raw `PreModel` interprets function types as meta-level functions.
For extensional equality with argument congruence to be sound, admissible
function values must respect the recursively defined `PreModel.Eqv` relation on
their arguments.  The full canonical carrier construction should eventually
source this law; this file records the first bridge theorem under exactly that
source condition.
-/

/-- Admissible function values respect `PreModel.Eqv` in their arguments. -/
def EqvArgumentCongruent
    (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  ∀ {σ τ : Ty Base}
    {f : Ty.denote M.Carrier (σ ⇒ τ)}
    {x y : Ty.denote M.Carrier σ},
      M.adm (σ ⇒ τ) f →
      M.adm σ x →
      M.adm σ y →
      PreModel.Eqv M.toPreModel σ x y →
        PreModel.Eqv M.toPreModel τ (f x) (f y)

/-- A semantic arrow value is realized when it respects `PreModel.Eqv` on
admissible arguments. -/
def RealizedArrow
    (M : HenkinModel.{u, v, w} Base Const) {σ τ : Ty Base}
    (f : Ty.denote M.Carrier (σ ⇒ τ)) : Prop :=
  ∀ {x y : Ty.denote M.Carrier σ},
    M.adm σ x →
    M.adm σ y →
    PreModel.Eqv M.toPreModel σ x y →
      PreModel.Eqv M.toPreModel τ (f x) (f y)

/-- The model's admissible arrow values are exactly disciplined enough for
argument-congruence soundness. -/
def RealizedArrowAdmissible
    (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  ∀ {σ τ : Ty Base} {f : Ty.denote M.Carrier (σ ⇒ τ)},
    M.adm (σ ⇒ τ) f → RealizedArrow M f

/-- Realized admissible arrows supply the argument-congruence side condition
used by the closed-term equality bridge. -/
theorem realizedArrowAdmissible_eqvArgumentCongruent
    {M : HenkinModel.{u, v, w} Base Const}
    (hReal : RealizedArrowAdmissible M) :
    EqvArgumentCongruent M := by
  intro σ τ f x y hf hx hy hxy
  exact hReal hf hx hy hxy

/-- The explicit realized-arrow formulation is equivalent to the older
argument-congruence side condition. -/
theorem realizedArrowAdmissible_iff_eqvArgumentCongruent
    {M : HenkinModel.{u, v, w} Base Const} :
    RealizedArrowAdmissible M ↔ EqvArgumentCongruent M := by
  constructor
  · exact realizedArrowAdmissible_eqvArgumentCongruent
  · intro hArg σ τ f hf x y hx hy hxy
    exact hArg hf hx hy hxy

/-- A Henkin model satisfies every sentence in a closed theory set. -/
def ModelsClosedTheorySet
    (M : HenkinModel.{u, v, w} Base Const)
    (T : ClosedTheorySet Const) : Prop :=
  ∀ φ : ClosedFormula Const, φ ∈ T → HenkinModel.models M φ

namespace ClosedTermPreModelBridge

variable {M : HenkinModel.{u, v, w} Base Const}

/-- The canonical empty valuation used for closed-term denotations. -/
def emptyValuation (M : HenkinModel.{u, v, w} Base Const) :
    HenkinModel.Valuation M ([] : Ctx Base)
  | _, v => nomatch v

@[simp] theorem emptyValuation_eq_nomatch
    (M : HenkinModel.{u, v, w} Base Const) :
    (emptyValuation M : HenkinModel.Valuation M ([] : Ctx Base)) =
      (fun {_τ} v => nomatch v) := by
  funext τ v
  nomatch v

/-- A semantic value is represented by a specific closed term when it is exactly
that term's denotation under the empty valuation. -/
def RepresentsClosedTerm
    (M : HenkinModel.{u, v, w} Base Const)
    {τ : Ty Base} (t : ClosedTerm Const τ)
    (x : Ty.denote M.Carrier τ) : Prop :=
  x = HenkinModel.denote M t (emptyValuation M)

/-- A semantic value is represented when some closed term denotes it.  This is
the lightweight relation needed before attempting a full quotient-carrier
canonical `PreModel`. -/
def RepresentedValue
    (M : HenkinModel.{u, v, w} Base Const)
    {τ : Ty Base} (x : Ty.denote M.Carrier τ) : Prop :=
  ∃ t : ClosedTerm Const τ, RepresentsClosedTerm M t x

@[simp] theorem representsClosedTerm_denote
    (M : HenkinModel.{u, v, w} Base Const)
    {τ : Ty Base} (t : ClosedTerm Const τ) :
    RepresentsClosedTerm M t
      (HenkinModel.denote M t (emptyValuation M)) :=
  rfl

theorem representedValue_denote
    (M : HenkinModel.{u, v, w} Base Const)
    {τ : Ty Base} (t : ClosedTerm Const τ) :
    RepresentedValue M
      (HenkinModel.denote M t (emptyValuation M)) :=
  ⟨t, representsClosedTerm_denote M t⟩

theorem representsClosedTerm_admissible
    {τ : Ty Base} {t : ClosedTerm Const τ}
    {x : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x) :
    M.adm τ x := by
  rw [hx]
  exact HenkinModel.denote_admissible M
    (by intro _ v; nomatch v) t

theorem representedValue_admissible
    {τ : Ty Base} {x : Ty.denote M.Carrier τ}
    (hx : RepresentedValue M x) :
    M.adm τ x := by
  rcases hx with ⟨t, ht⟩
  exact representsClosedTerm_admissible (M := M) (t := t) ht

/-- Closed application preserves closed-term representation. -/
theorem representsClosedTerm_app
    {σ τ : Ty Base}
    {F : ClosedTerm Const (σ ⇒ τ)}
    {t : ClosedTerm Const σ}
    {f : Ty.denote M.Carrier (σ ⇒ τ)}
    {x : Ty.denote M.Carrier σ}
    (hF : RepresentsClosedTerm M F f)
    (hx : RepresentsClosedTerm M t x) :
    RepresentsClosedTerm M (.app F t) (f x) := by
  unfold RepresentsClosedTerm at hF hx ⊢
  rw [hF, hx]
  rfl

/-- Laws saying that a semantic carrier is controlled by closed-term
representatives.  This is the precise non-circular obligation the future
canonical quotient carrier must provide before it can supply realized-arrow
admissibility to the raw `PreModel` layer. -/
structure RepresentedCarrierLaws
    (M : HenkinModel.{u, v, w} Base Const)
    (T : ClosedTheorySet Const) : Prop where
  all_admissible_represented :
    ∀ {τ : Ty Base} (x : Ty.denote M.Carrier τ),
      M.adm τ x → RepresentedValue M x
  eqv_reflects_closedTermEq :
    ∀ {τ : Ty Base} {t u : ClosedTerm Const τ}
      {x y : Ty.denote M.Carrier τ},
      RepresentsClosedTerm M t x →
      RepresentsClosedTerm M u y →
      PreModel.Eqv M.toPreModel τ x y →
        ClosedTermEq (Const := Const) T t u
  closedTermEq_sound :
    ∀ {τ : Ty Base} {t u : ClosedTerm Const τ}
      {x y : Ty.denote M.Carrier τ},
      RepresentsClosedTerm M t x →
      RepresentsClosedTerm M u y →
      ClosedTermEq (Const := Const) T t u →
        PreModel.Eqv M.toPreModel τ x y

/-- A semantic model realizes the canonical closed-term quotient carrier when
quotient classes can be mapped into semantic values, every admissible semantic
value is in that image, closed representatives denote their own classes, and
semantic equivalence reflects quotient equality.

This isolates the exact additional data needed to turn the concrete
closed-term quotient carrier into the represented-carrier source required by
the raw `PreModel` soundness bridge. -/
structure QuotientRealization
    (M : HenkinModel.{u, v, w} Base Const)
    (T : ClosedTheorySet Const) where
  realize :
    ∀ {τ : Ty Base},
      ClosedTermEq.Quot (Const := Const) T τ → Ty.denote M.Carrier τ
  realize_admissible :
    ∀ {τ : Ty Base} (q : ClosedTermEq.Quot (Const := Const) T τ),
      M.adm τ (realize q)
  realize_classOf :
    ∀ {τ : Ty Base} (t : ClosedTerm Const τ),
      realize (ClosedTermEq.classOf (T := T) t) =
        HenkinModel.denote M t (emptyValuation M)
  all_admissible_in_range :
    ∀ {τ : Ty Base} (x : Ty.denote M.Carrier τ),
      M.adm τ x →
        ∃ q : ClosedTermEq.Quot (Const := Const) T τ, x = realize q
  eqv_reflects_quotient_eq :
    ∀ {τ : Ty Base}
      {q r : ClosedTermEq.Quot (Const := Const) T τ},
      PreModel.Eqv M.toPreModel τ (realize q) (realize r) →
        q = r

/-- Quotient realizations supply represented semantic values. -/
theorem quotientRealization_representedValue
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {τ : Ty Base} {x : Ty.denote M.Carrier τ}
    (hx : M.adm τ x) :
    RepresentedValue M x := by
  rcases R.all_admissible_in_range x hx with ⟨q, hq⟩
  rcases ClosedTermEq.quotRepresentedValue (T := T) q with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  unfold RepresentsClosedTerm
  rw [hq, ht, R.realize_classOf]

/-- A quotient realization turns quotient equality reflection into closed-term
equality reflection. -/
theorem quotientRealization_reflects_closedTermEq
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {τ : Ty Base} {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y)
    (hxy : PreModel.Eqv M.toPreModel τ x y) :
    ClosedTermEq (Const := Const) T t u := by
  have hxy' :
      PreModel.Eqv M.toPreModel τ
        (R.realize (ClosedTermEq.classOf (T := T) t))
        (R.realize (ClosedTermEq.classOf (T := T) u)) := by
    rw [R.realize_classOf t, R.realize_classOf u]
    rw [← hx, ← hy]
    exact hxy
  exact (ClosedTermEq.classOf_eq_iff (T := T)).1
    (R.eqv_reflects_quotient_eq hxy')

/-- Closed-term equality is sound for values represented through a quotient
realization. -/
theorem quotientRealization_closedTermEq_sound
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {τ : Ty Base} {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y)
    (htu : ClosedTermEq (Const := Const) T t u) :
    PreModel.Eqv M.toPreModel τ x y := by
  have hq :
      ClosedTermEq.classOf (T := T) t =
        ClosedTermEq.classOf (T := T) u :=
    (ClosedTermEq.classOf_eq_iff (T := T)).2 htu
  have hEqv :
      PreModel.Eqv M.toPreModel τ
        (R.realize (ClosedTermEq.classOf (T := T) t))
        (R.realize (ClosedTermEq.classOf (T := T) u)) := by
    rw [hq]
    exact HenkinModel.eqv_refl M
      (R.realize_admissible (ClosedTermEq.classOf (T := T) u))
  rw [R.realize_classOf t, R.realize_classOf u] at hEqv
  rw [hx, hy]
  exact hEqv

/-- Quotient truth of a represented closed proposition gives semantic truth of
the representing value.  This is the proposition case of the canonical truth
lemma, phrased at the realization boundary. -/
theorem quotientRealization_propTruth_to_represented_down
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {p : ClosedFormula Const}
    {x : Ty.denote M.Carrier propTy}
    (hx : RepresentsClosedTerm M p x) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) →
      x.down := by
  intro hp
  have hpTop : ClosedTermEq (Const := Const) T p (.top : ClosedFormula Const) :=
    (ClosedTermEq.prop_eq_top_iff (T := T)).2 hp
  have hEqv :
      PreModel.Eqv M.toPreModel propTy x
        (HenkinModel.denote M (.top : ClosedFormula Const) (emptyValuation M)) :=
    quotientRealization_closedTermEq_sound
      (M := M) R hx (representsClosedTerm_denote M (.top : ClosedFormula Const)) hpTop
  exact hEqv.2 trivial

/-- Semantic truth of a represented closed proposition reflects back to
quotient truth when the realization reflects quotient equality. -/
theorem quotientRealization_represented_down_to_propTruth
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {p : ClosedFormula Const}
    {x : Ty.denote M.Carrier propTy}
    (hx : RepresentsClosedTerm M p x) :
    x.down →
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) := by
  intro hxDown
  have hEqv :
      PreModel.Eqv M.toPreModel propTy
        (R.realize (ClosedTermEq.classOf (T := T) p))
        (R.realize (ClosedTermEq.classOf (T := T) (.top : ClosedFormula Const))) := by
    rw [R.realize_classOf p, R.realize_classOf (.top : ClosedFormula Const)]
    change (HenkinModel.denote M p (emptyValuation M)).down ↔ True
    constructor
    · intro _
      trivial
    · intro _
      rw [← hx]
      exact hxDown
  have hClass :
      ClosedTermEq.classOf (T := T) p =
        ClosedTermEq.classOf (T := T) (.top : ClosedFormula Const) :=
    R.eqv_reflects_quotient_eq hEqv
  exact (ClosedTermEq.propTruth_classOf_iff_eq_top (T := T)).2 hClass

/-- A quotient realization identifies quotient truth of a represented closed
proposition with semantic truth of its representing value. -/
theorem quotientRealization_propTruth_iff_represented_down
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {p : ClosedFormula Const}
    {x : Ty.denote M.Carrier propTy}
    (hx : RepresentsClosedTerm M p x) :
    ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) ↔
      x.down := by
  constructor
  · exact quotientRealization_propTruth_to_represented_down (M := M) R hx
  · exact quotientRealization_represented_down_to_propTruth (M := M) R hx

/-- A quotient realization identifies semantic satisfaction of a closed formula
with quotient truth of its syntactic proposition class. -/
theorem quotientRealization_models_iff_propTruth
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    (p : ClosedFormula Const) :
    HenkinModel.models M p ↔
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) := by
  have hTruth :
      ClosedTermEq.propTruth (T := T) (ClosedTermEq.classOf p) ↔
        (HenkinModel.denote M p (emptyValuation M)).down :=
    quotientRealization_propTruth_iff_represented_down
      (M := M) R (representsClosedTerm_denote M p)
  exact hTruth.symm

/-- Over a canonical world carrier, a quotient realization turns semantic
satisfaction into membership in the world. -/
theorem quotientRealization_models_iff_world_mem
    (W : ClosedTheorySet.World Const)
    (R : QuotientRealization M W.carrier)
    (p : ClosedFormula Const) :
    HenkinModel.models M p ↔ p ∈ W.carrier := by
  exact
    (quotientRealization_models_iff_propTruth (M := M) R p).trans
      (ClosedTermEq.propTruth_world_iff_mem (Const := Const) W p)

/-- A model realizing a canonical world satisfies every sentence in that
world's closed theory-set carrier. -/
theorem quotientRealization_modelsClosedTheorySet_world
    (W : ClosedTheorySet.World Const)
    (R : QuotientRealization M W.carrier) :
    ModelsClosedTheorySet M W.carrier := by
  intro p hp
  exact (quotientRealization_models_iff_world_mem (M := M) W R p).2 hp

/-- If a canonical world omits a closed formula, any model realizing that world
refutes the formula. -/
theorem quotientRealization_not_models_of_world_not_mem
    (W : ClosedTheorySet.World Const)
    (R : QuotientRealization M W.carrier)
    {p : ClosedFormula Const} :
    p ∉ W.carrier → ¬ HenkinModel.models M p := by
  intro hp hModel
  exact hp ((quotientRealization_models_iff_world_mem (M := M) W R p).1 hModel)

/-- A model realizing a canonical world satisfies a closed formula exactly when
the singleton canonical-world evidence gives that formula strength `1`. -/
theorem quotientRealization_models_iff_singleton_strength_one
    (W : ClosedTheorySet.World Const)
    (R : QuotientRealization M W.carrier)
    (p : ClosedFormula Const) :
    HenkinModel.models M p ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) p = 1 := by
  exact
    (quotientRealization_models_iff_world_mem (M := M) W R p).trans
      (singleton_adequacy_strength_one (Base := Base) (Const := Const) W p)

/-- A model realizing a canonical world refutes a closed formula exactly when
the singleton canonical-world evidence gives that formula strength `0`. -/
theorem quotientRealization_not_models_iff_singleton_strength_zero
    (W : ClosedTheorySet.World Const)
    (R : QuotientRealization M W.carrier)
    (p : ClosedFormula Const) :
    ¬ HenkinModel.models M p ↔
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) p = 0 := by
  rw [quotientRealization_models_iff_world_mem (M := M) W R p]
  exact singleton_adequacy_strength_zero (Base := Base) (Const := Const) W p

/-- A semantic realization of the canonical closed-term quotient carrier
supplies the represented-carrier laws required by the extensional soundness
bridge. -/
theorem quotientRealization_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T) :
    RepresentedCarrierLaws M T where
  all_admissible_represented := by
    intro τ x hx
    exact quotientRealization_representedValue (M := M) R hx
  eqv_reflects_closedTermEq := by
    intro τ t u x y hx hy hxy
    exact quotientRealization_reflects_closedTermEq (M := M) R hx hy hxy
  closedTermEq_sound := by
    intro τ t u x y hx hy htu
    exact quotientRealization_closedTermEq_sound (M := M) R hx hy htu

/-- A carrier controlled by closed-term representatives supplies the realized
arrow law needed by extensional soundness. -/
theorem representedCarrierLaws_realizedArrowAdmissible
    {T : ClosedTheorySet Const}
    (h : RepresentedCarrierLaws M T) :
    RealizedArrowAdmissible M := by
  intro σ τ f hf x y hx hy hxy
  rcases h.all_admissible_represented f hf with ⟨F, hF⟩
  rcases h.all_admissible_represented x hx with ⟨tx, htx⟩
  rcases h.all_admissible_represented y hy with ⟨ty, hty⟩
  have hxyClosed : ClosedTermEq (Const := Const) T tx ty :=
    h.eqv_reflects_closedTermEq htx hty hxy
  have hAppClosed :
      ClosedTermEq (Const := Const) T (.app F tx) (.app F ty) :=
    ClosedTermEq.app_arg (T := T) F hxyClosed
  exact h.closedTermEq_sound
    (representsClosedTerm_app (M := M) hF htx)
    (representsClosedTerm_app (M := M) hF hty)
    hAppClosed

/-- The same represented-carrier laws give the older argument-congruence
formulation directly. -/
theorem representedCarrierLaws_eqvArgumentCongruent
    {T : ClosedTheorySet Const}
    (h : RepresentedCarrierLaws M T) :
    EqvArgumentCongruent M :=
  realizedArrowAdmissible_eqvArgumentCongruent
    (representedCarrierLaws_realizedArrowAdmissible (M := M) h)

/-- A quotient realization sources realized-arrow admissibility for semantic
models. -/
theorem quotientRealization_realizedArrowAdmissible
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T) :
    RealizedArrowAdmissible M :=
  representedCarrierLaws_realizedArrowAdmissible
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R)

/-- A quotient realization sources the argument-congruence side condition used
by extensional equality soundness. -/
theorem quotientRealization_eqvArgumentCongruent
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T) :
    EqvArgumentCongruent M :=
  realizedArrowAdmissible_eqvArgumentCongruent
    (quotientRealization_realizedArrowAdmissible (M := M) R)

/-- Soundness for the extensional derivation overlay, assuming semantic
argument congruence for admissible function values. -/
theorem extDerivation_sound_of_eqvArgumentCongruent
    (hArg : EqvArgumentCongruent M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down := by
  induction d with
  | hyp hmem =>
      intro ρ hρ hΔ
      exact hΔ _ hmem
  | topI =>
      intro ρ hρ hΔ
      simp
  | botE h ih =>
      intro ρ hρ hΔ
      exact False.elim (ih hρ hΔ)
  | andI hφ hψ ihφ ihψ =>
      intro ρ hρ hΔ
      exact ⟨ihφ hρ hΔ, ihψ hρ hΔ⟩
  | andEL h ih =>
      intro ρ hρ hΔ
      exact (ih hρ hΔ).1
  | andER h ih =>
      intro ρ hρ hΔ
      exact (ih hρ hΔ).2
  | orIL h ih =>
      intro ρ hρ hΔ
      exact Or.inl (ih hρ hΔ)
  | orIR h ih =>
      intro ρ hρ hΔ
      exact Or.inr (ih hρ hΔ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro ρ hρ hΔ
      rcases ihor hρ hΔ with h | h
      · exact ihφ hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
      · exact ihψ hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
  | impI h ih =>
      intro ρ hρ hΔ hφ
      exact ih hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | impE himp hφ ihimp ihφ =>
      intro ρ hρ hΔ
      exact (ihimp hρ hΔ) (ihφ hρ hΔ)
  | notI h ih =>
      intro ρ hρ hΔ hφ
      exact ih hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | notE hnot hφ ihnot ihφ =>
      intro ρ hρ hΔ
      exact (ihnot hρ hΔ) (ihφ hρ hΔ)
  | allI h ih =>
      intro ρ hρ hΔ x hx
      exact ih (HenkinModel.extend_admissible M hρ hx)
        (Soundness.satisfies_weakenHyps M hΔ x)
  | allE t h ih =>
      intro ρ hρ hΔ
      have hall := ih hρ hΔ
      have ht : M.adm _ (HenkinModel.denote M t ρ) :=
        HenkinModel.denote_admissible M hρ t
      exact (Soundness.denote_instantiate M t _ ρ).mpr (hall _ ht)
  | exI t h ih =>
      intro ρ hρ hΔ
      refine ⟨HenkinModel.denote M t ρ, HenkinModel.denote_admissible M hρ t, ?_⟩
      exact (Soundness.denote_instantiate M t _ ρ).mp (ih hρ hΔ)
  | exE hex hbody ihex ihbody =>
      intro ρ hρ hΔ
      rcases ihex hρ hΔ with ⟨x, hx, hφ⟩
      have hbody' :=
        ihbody (HenkinModel.extend_admissible M hρ hx) (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · exact hφ
          · exact Soundness.satisfies_weakenHyps M hΔ x _ hχ)
      simpa using hbody'
  | eqRefl t =>
      intro ρ hρ hΔ
      exact HenkinModel.eqv_refl M (HenkinModel.denote_admissible M hρ t)
  | eqSymm h ih =>
      intro ρ hρ hΔ
      exact HenkinModel.eqv_symm M (ih hρ hΔ)
  | eqTrans htu huv ihtu ihuv =>
      intro ρ hρ hΔ
      exact HenkinModel.eqv_trans M (ihtu hρ hΔ) (ihuv hρ hΔ)
  | eqPropI hpq hqp ihpq ihqp =>
      intro ρ hρ hΔ
      exact ⟨ihpq hρ hΔ, ihqp hρ hΔ⟩
  | eqPropEL hpq ih =>
      intro ρ hρ hΔ
      exact (ih hρ hΔ).1
  | eqPropER hpq ih =>
      intro ρ hρ hΔ
      exact (ih hρ hΔ).2
  | eqApp t h ih =>
      intro ρ hρ hΔ
      exact HenkinModel.eqv_arr_apply M (ih hρ hΔ)
        (HenkinModel.denote_admissible M hρ t)
  | eqAppArg f h ih =>
      intro ρ hρ hΔ
      exact hArg
        (HenkinModel.denote_admissible M hρ f)
        (HenkinModel.denote_admissible M hρ _)
        (HenkinModel.denote_admissible M hρ _)
        (ih hρ hΔ)
  | eqLam h ih =>
      intro ρ hρ hΔ x hx
      exact ih (HenkinModel.extend_admissible M hρ hx)
        (Soundness.satisfies_weakenHyps M hΔ x)
  | funExt h ih =>
      intro ρ hρ hΔ x hx
      have hpoint := ih hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
        using hpoint
  | beta t u =>
      intro ρ hρ hΔ
      simpa [HenkinModel.denote, PreModel.denote] using
        HenkinModel.eqv_refl M
          (HenkinModel.denote_admissible M hρ (instantiate (Base := Base) t u))
  | eta f =>
      intro ρ hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend] using
        (HenkinModel.eqv_refl M
          (M.app_mem (HenkinModel.denote_admissible M hρ f) hx))

/-- Soundness for the extensional derivation overlay, using the explicit
realized-arrow admissibility formulation. -/
theorem extDerivation_sound_of_realizedArrowAdmissible
    (hReal : RealizedArrowAdmissible M)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down :=
  extDerivation_sound_of_eqvArgumentCongruent
    (M := M) (realizedArrowAdmissible_eqvArgumentCongruent hReal) d

/-- Soundness for the extensional derivation overlay, sourced from represented
closed-term carrier laws. -/
theorem extDerivation_sound_of_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (hLaws : RepresentedCarrierLaws M T)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down :=
  extDerivation_sound_of_realizedArrowAdmissible
    (M := M) (representedCarrierLaws_realizedArrowAdmissible (M := M) hLaws) d

/-- Soundness for the extensional derivation overlay, sourced from a semantic
realization of the canonical closed-term quotient carrier. -/
theorem extDerivation_sound_of_quotientRealization
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      Soundness.SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down :=
  extDerivation_sound_of_representedCarrierLaws
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R) d

/-- Finite provability from a theory set is sound in any Henkin model satisfying
the theory, provided the model has semantic argument congruence. -/
theorem closedTheorySet_provable_sound_of_eqvArgumentCongruent
    (hArg : EqvArgumentCongruent M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {φ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) T φ →
      HenkinModel.models M φ := by
  rintro ⟨Δ, hΔ, hφ⟩
  exact extDerivation_sound_of_eqvArgumentCongruent
    (M := M) hArg hφ
    (ρ := emptyValuation M)
    (by intro τ v; nomatch v)
    (by
      intro ψ hψ
      exact hT ψ (hΔ ψ hψ))

/-- Finite provability from a theory set is sound in any Henkin model satisfying
the theory, using realized-arrow admissibility as the semantic arrow law. -/
theorem closedTheorySet_provable_sound_of_realizedArrowAdmissible
    (hReal : RealizedArrowAdmissible M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {φ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) T φ →
      HenkinModel.models M φ :=
  closedTheorySet_provable_sound_of_eqvArgumentCongruent
    (M := M) (realizedArrowAdmissible_eqvArgumentCongruent hReal) hT

/-- Finite provability from a theory set is sound when the carrier is governed
by represented closed-term laws. -/
theorem closedTheorySet_provable_sound_of_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (hLaws : RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T) {φ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) T φ →
      HenkinModel.models M φ :=
  closedTheorySet_provable_sound_of_realizedArrowAdmissible
    (M := M) (representedCarrierLaws_realizedArrowAdmissible (M := M) hLaws) hT

/-- Finite provability from a theory set is sound when a semantic model realizes
the canonical closed-term quotient carrier. -/
theorem closedTheorySet_provable_sound_of_quotientRealization
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T) {φ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) T φ →
      HenkinModel.models M φ :=
  closedTheorySet_provable_sound_of_representedCarrierLaws
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R) hT

/-- Provable equality in a closed theory set implies semantic `PreModel.Eqv`
between the denotations of the closed terms. -/
theorem closedTheorySet_provable_eq_to_preModel_eqv
    (hArg : EqvArgumentCongruent M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTheorySet.Provable (Const := Const) T (.eq t u) →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) := by
  intro hEq
  change PreModel.Eqv M.toPreModel τ
    (HenkinModel.denote M t (emptyValuation M))
    (HenkinModel.denote M u (emptyValuation M))
  exact closedTheorySet_provable_sound_of_eqvArgumentCongruent
    (M := M) hArg hT hEq

/-- Provable equality in a closed theory set implies semantic `PreModel.Eqv`
under the explicit realized-arrow admissibility side condition. -/
theorem closedTheorySet_provable_eq_to_preModel_eqv_of_realizedArrowAdmissible
    (hReal : RealizedArrowAdmissible M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTheorySet.Provable (Const := Const) T (.eq t u) →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTheorySet_provable_eq_to_preModel_eqv
    (M := M) (realizedArrowAdmissible_eqvArgumentCongruent hReal) hT

/-- Provable equality in a closed theory set gives semantic `PreModel.Eqv`
when represented carrier laws source the arrow congruence side condition. -/
theorem closedTheorySet_provable_eq_to_preModel_eqv_of_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (hLaws : RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTheorySet.Provable (Const := Const) T (.eq t u) →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTheorySet_provable_eq_to_preModel_eqv_of_realizedArrowAdmissible
    (M := M) (representedCarrierLaws_realizedArrowAdmissible (M := M) hLaws) hT

/-- Provable equality in a closed theory set gives semantic `PreModel.Eqv`
when the model realizes the canonical closed-term quotient carrier. -/
theorem closedTheorySet_provable_eq_to_preModel_eqv_of_quotientRealization
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTheorySet.Provable (Const := Const) T (.eq t u) →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTheorySet_provable_eq_to_preModel_eqv_of_representedCarrierLaws
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R) hT

/-- The first explicit bridge from quotient-side closed-term equality to
semantic `PreModel.Eqv`. -/
theorem closedTermEq_to_preModel_eqv
    (hArg : EqvArgumentCongruent M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTheorySet_provable_eq_to_preModel_eqv (M := M) hArg hT

/-- Closed-term equality transports to semantic `PreModel.Eqv` between any
semantic values represented by the two closed terms. -/
theorem represented_closedTermEq_to_preModel_eqv
    (hArg : EqvArgumentCongruent M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y) :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ x y := by
  intro hEq
  rw [hx, hy]
  exact closedTermEq_to_preModel_eqv (M := M) hArg hT hEq

/-- The closed-term equality bridge under realized-arrow admissibility. -/
theorem closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (hReal : RealizedArrowAdmissible M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTermEq_to_preModel_eqv
    (M := M) (realizedArrowAdmissible_eqvArgumentCongruent hReal) hT

/-- The closed-term equality bridge sourced by represented carrier laws. -/
theorem closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (hLaws : RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (M := M) (representedCarrierLaws_realizedArrowAdmissible (M := M) hLaws) hT

/-- The closed-term equality bridge sourced by a realization of the canonical
closed-term quotient carrier. -/
theorem closedTermEq_to_preModel_eqv_of_quotientRealization
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ} :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ
        (HenkinModel.denote M t (emptyValuation M))
        (HenkinModel.denote M u (emptyValuation M)) :=
  closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R) hT

/-- Represented closed-term equality transports to semantic `PreModel.Eqv`
under realized-arrow admissibility. -/
theorem represented_closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (hReal : RealizedArrowAdmissible M) {T : ClosedTheorySet Const}
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y) :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ x y :=
  represented_closedTermEq_to_preModel_eqv
    (M := M) (realizedArrowAdmissible_eqvArgumentCongruent hReal) hT hx hy

/-- Represented closed-term equality transports to semantic `PreModel.Eqv`
when represented carrier laws source the arrow congruence side condition. -/
theorem represented_closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    {T : ClosedTheorySet Const}
    (hLaws : RepresentedCarrierLaws M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y) :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ x y :=
  represented_closedTermEq_to_preModel_eqv_of_realizedArrowAdmissible
    (M := M) (representedCarrierLaws_realizedArrowAdmissible (M := M) hLaws) hT hx hy

/-- Represented closed-term equality transports to semantic `PreModel.Eqv`
when a quotient realization sources the represented-carrier laws. -/
theorem represented_closedTermEq_to_preModel_eqv_of_quotientRealization
    {T : ClosedTheorySet Const}
    (R : QuotientRealization M T)
    (hT : ModelsClosedTheorySet M T) {τ : Ty Base}
    {t u : ClosedTerm Const τ}
    {x y : Ty.denote M.Carrier τ}
    (hx : RepresentsClosedTerm M t x)
    (hy : RepresentsClosedTerm M u y) :
    ClosedTermEq (Const := Const) T t u →
      PreModel.Eqv M.toPreModel τ x y :=
  represented_closedTermEq_to_preModel_eqv_of_representedCarrierLaws
    (M := M) (quotientRealization_representedCarrierLaws (M := M) R) hT hx hy

end ClosedTermPreModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
