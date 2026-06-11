import Mettapedia.Logic.HOL.TermModel.Realize
import Mettapedia.Logic.HOL.TermModel.Truth
import Mettapedia.Logic.HOL.Syntax.FreshConst

/-!
# Term denotation and reification for the canonical general model

Over `WithParams Const` (every type is inhabited by a parameter constant), we define
the denotation `tval τ : ClosedTerm τ → ⟦τ⟧` (recursion on type) and its partial
inverse `treify τ : ⟦τ⟧ → ClosedTerm τ` (representative of an admissible element,
chosen by `Classical.choice`).  The key correctness facts —
`Rep (tval τ t) t` and the uniqueness/`eq`-respecting lemmas — are proved together by
induction on the type.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

open Mettapedia.Logic.HOL.WithParams
open scoped Classical

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- A canonical closed inhabitant of every type (a parameter constant). -/
def defaultTerm (τ : Ty Base) : ClosedTerm (WithParams Const) τ := .const (param τ 0)

/-- Reify a semantic element to a representing closed term (the chosen representative
if admissible, else the default).  Used only on admissible elements. -/
noncomputable def treify (M : World (WithParams Const)) :
    (τ : Ty Base) → Ty.denote (termCarrier M) τ → ClosedTerm (WithParams Const) τ :=
  fun τ d => if h : admissible M τ d then h.choose else defaultTerm τ

theorem rep_treify (M : World (WithParams Const)) {τ : Ty Base}
    {d : Ty.denote (termCarrier M) τ} (h : admissible M τ d) :
    Rep M τ d (treify M τ d) := by
  rw [treify, dif_pos h]
  exact h.choose_spec

/-- Denotation of a closed term in the canonical general model, by recursion on type:
`prop ↦ truth = membership`, `base ↦ quotient class`, `arr ↦ apply to the reified
argument`. -/
noncomputable def tval (M : World (WithParams Const)) :
    (τ : Ty Base) → ClosedTerm (WithParams Const) τ → Ty.denote (termCarrier M) τ
  | .prop, t => ULift.up (t ∈ M.carrier)
  | .base b, t => (ULift.up (TermDom.mk M t) : termCarrier M b)
  | .arr σ ρ, t => fun x => tval M ρ (.app t (treify M σ x))

/-! ## Realization respects provable equality -/

theorem Rep_respects_eq (M : World (WithParams Const)) :
    ∀ (τ : Ty Base) {d : Ty.denote (termCarrier M) τ}
      {s s' : ClosedTerm (WithParams Const) τ},
      (.eq s s' : ClosedFormula (WithParams Const)) ∈ M.carrier → Rep M τ d s → Rep M τ d s'
  | .prop, d, s, s', heq, hrep => by
      simp only [Rep] at hrep ⊢
      exact hrep.trans (eqProp_mem_iff heq)
  | .base b, d, s, s', heq, hrep => by
      simp only [Rep] at hrep ⊢
      rw [hrep]
      exact congrArg ULift.up (TermDom.mk_eq.mpr heq)
  | .arr σ ρ, d, s, s', heq, hrep => by
      simp only [Rep] at hrep ⊢
      intro a u ha
      exact Rep_respects_eq M ρ (World.eq_app_mem u heq) (hrep a u ha)

/-! ## Propositional extensionality converse (for the `prop`-fiber uniqueness) -/

theorem provable_eqProp_intro {T : ClosedTheorySet (WithParams Const)}
    {φ ψ : ClosedFormula (WithParams Const)}
    (h1 : Provable (Const := WithParams Const) T (.imp φ ψ))
    (h2 : Provable (Const := WithParams Const) T (.imp ψ φ)) :
    Provable (Const := WithParams Const) T (.eq φ ψ) := by
  rcases h1 with ⟨Γ1, hΓ1, d1⟩
  rcases h2 with ⟨Γ2, hΓ2, d2⟩
  refine ⟨Γ1 ++ Γ2, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with h | h
    · exact hΓ1 ξ h
    · exact hΓ2 ξ h
  · exact ExtDerivation.eqPropI
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inl hξ)) d1)
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inr hξ)) d2)

theorem eqProp_mem_of_iff (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier)
    {φ ψ : ClosedFormula (WithParams Const)} (h : φ ∈ M.carrier ↔ ψ ∈ M.carrier) :
    (.eq φ ψ : ClosedFormula (WithParams Const)) ∈ M.carrier :=
  World.mem_of_provable (W := M)
    (provable_eqProp_intro
      (provable_of_mem (imp_mem M hC h.mp))
      (provable_of_mem (imp_mem M hC h.mpr)))

/-- Functional extensionality at the membership level: if `u₁ w = u₂ w` is in `M`
for every closed argument `w`, then `u₁ = u₂` is in `M`. -/
theorem eq_of_app_eq (M : World (WithParams Const)) {σ ρ : Ty Base}
    {u₁ u₂ : ClosedTerm (WithParams Const) (σ ⇒ ρ)}
    (h : ∀ w : ClosedTerm (WithParams Const) σ,
      (.eq (.app u₁ w) (.app u₂ w) : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    (.eq u₁ u₂ : ClosedFormula (WithParams Const)) ∈ M.carrier := by
  apply World.eq_funext_mem
  rw [World.mem_all_iff]
  intro w
  have key : ∀ (u : ClosedTerm (WithParams Const) (σ ⇒ ρ)),
      instantiate (Base := Base) w (.app (weaken (Base := Base) (σ := σ) u) (.var .vz))
        = (.app u w : ClosedTerm (WithParams Const) ρ) := by
    intro u
    show (.app (instantiate (Base := Base) w (weaken (Base := Base) (σ := σ) u))
              (instantiate (Base := Base) w (.var .vz)) : ClosedTerm (WithParams Const) ρ) = .app u w
    rw [instantiate_weaken, instantiate_var_vz]
  show (.eq (instantiate (Base := Base) w (.app (weaken (Base := Base) (σ := σ) u₁) (.var .vz)))
            (instantiate (Base := Base) w (.app (weaken (Base := Base) (σ := σ) u₂) (.var .vz)))
        : ClosedFormula (WithParams Const)) ∈ M.carrier
  rw [key u₁, key u₂]
  exact h w

/-! ## Realization correctness: `tval` represents, and representatives are unique -/

/-- The denotation `tval τ t` is represented by `t`, and any two closed terms
representing the same element are provably equal — proved together by type induction.
The `arr` cases close the loop via `treify`, `eq_of_app_eq` (functional extensionality)
and `Rep_respects_eq`. -/
theorem repCore (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    ∀ (τ : Ty Base),
      (∀ t : ClosedTerm (WithParams Const) τ, Rep M τ (tval M τ t) t) ∧
      (∀ {d : Ty.denote (termCarrier M) τ} {u₁ u₂ : ClosedTerm (WithParams Const) τ},
        Rep M τ d u₁ → Rep M τ d u₂ →
        (.eq u₁ u₂ : ClosedFormula (WithParams Const)) ∈ M.carrier)
  | .prop => by
      refine ⟨fun t => by simp only [tval, Rep], fun {d u₁ u₂} h1 h2 => ?_⟩
      simp only [Rep] at h1 h2
      exact eqProp_mem_of_iff M hC (h1.symm.trans h2)
  | .base b => by
      refine ⟨fun t => by simp only [tval, Rep], fun {d u₁ u₂} h1 h2 => ?_⟩
      simp only [Rep] at h1 h2
      rw [h1] at h2
      exact TermDom.mk_eq.mp (congrArg ULift.down h2)
  | .arr σ ρ => by
      have ihσ := repCore M hC σ
      have ihρ := repCore M hC ρ
      refine ⟨fun t => ?_, fun {d u₁ u₂} h1 h2 => ?_⟩
      · simp only [Rep]
        intro d u hdu
        simp only [tval]
        have hadm : admissible M σ d := ⟨u, hdu⟩
        have heq : (.eq u (treify M σ d) : ClosedFormula (WithParams Const)) ∈ M.carrier :=
          ihσ.2 hdu (rep_treify M hadm)
        exact Rep_respects_eq M ρ (World.eq_symm_mem (World.eq_appArg_mem t heq))
          (ihρ.1 (.app t (treify M σ d)))
      · simp only [Rep] at h1 h2
        refine eq_of_app_eq M (fun w => ?_)
        exact ihρ.2 (h1 (tval M σ w) w (ihσ.1 w)) (h2 (tval M σ w) w (ihσ.1 w))

/-- `tval τ t` is represented by `t` (the existence half of `repCore`). -/
theorem rep_tval (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier)
    {τ : Ty Base} (t : ClosedTerm (WithParams Const) τ) : Rep M τ (tval M τ t) t :=
  (repCore M hC τ).1 t

end ClosedTheorySet
end Mettapedia.Logic.HOL
