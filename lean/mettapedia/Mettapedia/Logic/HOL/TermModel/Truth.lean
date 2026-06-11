import Mettapedia.Logic.HOL.TermModel.Domain

/-!
# The canonical term-model truth lemma

The heart of completeness.  Over a **complete** world `M`, the canonical 2-valued
term-model truth value of a formula `φ` under a *closed-term environment*
`ρ : Subst Const Γ []` coincides with membership of `subst ρ φ` in `M`:

  `Truth M φ ρ ↔ subst ρ φ ∈ M.carrier`.

`Truth` recurses **structurally on the term** (carrying the substitution in `ρ`),
so the `∀`/`∃` cases reduce to closed-term instances via `World.mem_all_iff` /
`World.mem_ex_iff` and the substitution lemma `instantiate_subst_lift` — never
recursing on an instantiated formula.  This is exactly what dodges the
prop-typed-quantifier trap.  The `imp`/`not` cases use the world's completeness.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- Extend a closed-term environment by one closed term at the front. -/
def extendEnv {Γ : Ctx Base} {σ : Ty Base} (ρ : Subst Const Γ [])
    (t : ClosedTerm Const σ) : Subst Const (σ :: Γ) []
  | _, .vz => t
  | _, .vs v => ρ v

/-- Instantiating the top variable of a `lift`-substituted body equals substituting
under the extended closed-term environment. -/
theorem instantiate_subst_lift {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : Subst Const Γ []) (t : ClosedTerm Const σ) (ψ : Term Const (σ :: Γ) τ) :
    instantiate (Base := Base) t (subst (Subst.lift (Base := Base) ρ) ψ)
      = subst (extendEnv ρ t) ψ := by
  unfold instantiate
  rw [subst_comp]
  apply subst_ext
  intro τ v
  cases v with
  | vz => rfl
  | vs w => exact instantiate_weaken t (ρ w)

/-! ## Classical `imp`/`not` membership (using world completeness) -/

theorem provable_imp_intro_right {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (h : Provable (Const := Const) T ψ) : Provable (Const := Const) T (.imp φ ψ) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.impI
    (ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) d)⟩

theorem provable_imp_of_not_left {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (h : Provable (Const := Const) T (.not φ)) : Provable (Const := Const) T (.imp φ ψ) := by
  rcases h with ⟨Γ, hΓ, d⟩
  refine ⟨Γ, hΓ, ExtDerivation.impI ?_⟩
  apply ExtDerivation.botE
  exact ExtDerivation.notE
    (ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) d)
    (ExtDerivation.hyp List.mem_cons_self)

theorem not_mem_iff (M : World Const)
    (hC : ∀ χ : ClosedFormula Const, χ ∈ M.carrier ∨ (.not χ : ClosedFormula Const) ∈ M.carrier)
    {φ : ClosedFormula Const} :
    (.not φ : ClosedFormula Const) ∈ M.carrier ↔ φ ∉ M.carrier := by
  constructor
  · intro hn hφ
    exact M.consistent (provable_bot_of_not (provable_of_mem hn) (provable_of_mem hφ))
  · intro hφ
    exact (hC φ).resolve_left hφ

theorem imp_mem (M : World Const)
    (hC : ∀ χ : ClosedFormula Const, χ ∈ M.carrier ∨ (.not χ : ClosedFormula Const) ∈ M.carrier)
    {φ ψ : ClosedFormula Const} (h : φ ∈ M.carrier → ψ ∈ M.carrier) :
    (.imp φ ψ : ClosedFormula Const) ∈ M.carrier := by
  rcases hC φ with hφ | hnφ
  · exact M.closed (provable_imp_intro_right (provable_of_mem (h hφ)))
  · exact M.closed (provable_imp_of_not_left (provable_of_mem hnφ))

/-! ## The truth predicate and the truth lemma -/

/-- Truth of a formula in the canonical term model under a closed-term environment.
Recurses structurally on the term. -/
def Truth (M : World Const) :
    {Γ : Ctx Base} → Formula Const Γ → Subst Const Γ [] → Prop
  | _, .var v, ρ => (subst ρ (.var v) : ClosedFormula Const) ∈ M.carrier
  | _, .const c, ρ => (subst ρ (.const c) : ClosedFormula Const) ∈ M.carrier
  | _, .app f a, ρ => (subst ρ (.app f a) : ClosedFormula Const) ∈ M.carrier
  | _, .eq s u, ρ => (subst ρ (.eq s u) : ClosedFormula Const) ∈ M.carrier
  | _, .top, _ => True
  | _, .bot, _ => False
  | _, .and a b, ρ => Truth M a ρ ∧ Truth M b ρ
  | _, .or a b, ρ => Truth M a ρ ∨ Truth M b ρ
  | _, .imp a b, ρ => Truth M a ρ → Truth M b ρ
  | _, .not a, ρ => ¬ Truth M a ρ
  | _, .all ψ, ρ => ∀ t, Truth M ψ (extendEnv ρ t)
  | _, .ex ψ, ρ => ∃ t, Truth M ψ (extendEnv ρ t)

/-- **Truth lemma.**  Over a complete world `M`, truth in the canonical term model is
membership of the substituted formula. -/
theorem truth (M : World Const)
    (hC : ∀ χ : ClosedFormula Const, χ ∈ M.carrier ∨ (.not χ : ClosedFormula Const) ∈ M.carrier) :
    ∀ {Γ : Ctx Base} (φ : Formula Const Γ) (ρ : Subst Const Γ []),
      Truth M φ ρ ↔ (subst ρ φ : ClosedFormula Const) ∈ M.carrier
  | _, .var v, ρ => by simp only [Truth]
  | _, .const c, ρ => by simp only [Truth]
  | _, .app f a, ρ => by simp only [Truth]
  | _, .eq s u, ρ => by simp only [Truth]
  | _, .top, ρ => by
      simp only [Truth, subst]
      exact iff_of_true trivial World.top_mem
  | _, .bot, ρ => by
      simp only [Truth, subst]
      exact iff_of_false not_false World.bot_not_mem
  | _, .and a b, ρ => by
      simp only [Truth, subst]
      rw [truth M hC a ρ, truth M hC b ρ]
      exact ⟨fun ⟨ha, hb⟩ => World.and_mem ha hb,
             fun h => ⟨World.and_left_mem h, World.and_right_mem h⟩⟩
  | _, .or a b, ρ => by
      simp only [Truth, subst]
      rw [truth M hC a ρ, truth M hC b ρ]
      exact ⟨fun h => h.elim (fun ha => World.or_left_mem ha) (fun hb => World.or_right_mem hb),
             fun h => M.prime_or h⟩
  | _, .imp a b, ρ => by
      simp only [Truth, subst]
      rw [truth M hC a ρ, truth M hC b ρ]
      exact ⟨fun h => imp_mem M hC h, fun h ha => World.mp h ha⟩
  | _, .not a, ρ => by
      simp only [Truth, subst]
      rw [truth M hC a ρ]
      exact (not_mem_iff M hC).symm
  | _, .all ψ, ρ => by
      simp only [Truth, subst]
      rw [World.mem_all_iff]
      apply forall_congr'
      intro t
      rw [truth M hC ψ (extendEnv ρ t), instantiate_subst_lift]
  | _, .ex ψ, ρ => by
      simp only [Truth, subst]
      rw [World.mem_ex_iff]
      apply exists_congr
      intro t
      rw [truth M hC ψ (extendEnv ρ t), instantiate_subst_lift]

end ClosedTheorySet
end Mettapedia.Logic.HOL
