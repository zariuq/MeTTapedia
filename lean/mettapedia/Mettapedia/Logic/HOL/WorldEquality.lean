import Mettapedia.Logic.HOL.CanonicalQuantifierBridges

/-!
# Equality bridges over a world

The canonical term model's domain is the quotient of closed terms by the equality
predicate `(.eq s t) ∈ W.carrier`.  For that to be a setoid and for the
extensional-equality lemma to go through, the world must be closed under the
equality rules of `ExtDerivation`.  This file provides those bridges, each a
one-liner `mem_of_provable ∘ <Provable eq-helper> ∘ provable_of_mem`:

* reflexivity / symmetry / transitivity (→ the term setoid);
* application congruence in both positions (`eq_app_mem`, `eq_appArg_mem`);
* functional extensionality (`eq_funext_mem`).
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## `Provable`-level equality helpers -/

theorem provable_eq_refl (T : ClosedTheorySet Const) {τ : Ty Base} (t : ClosedTerm Const τ) :
    Provable (Const := Const) T (.eq t t) := by
  refine ⟨[], ?_, ?_⟩
  · intro ψ hψ; cases hψ
  · exact ExtDerivation.eqRefl t

theorem provable_eq_symm {T : ClosedTheorySet Const} {τ : Ty Base} {s t : ClosedTerm Const τ}
    (h : Provable (Const := Const) T (.eq s t)) : Provable (Const := Const) T (.eq t s) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqSymm d⟩

theorem provable_eq_trans {T : ClosedTheorySet Const} {τ : Ty Base} {s t r : ClosedTerm Const τ}
    (hst : Provable (Const := Const) T (.eq s t)) (htr : Provable (Const := Const) T (.eq t r)) :
    Provable (Const := Const) T (.eq s r) := by
  rcases hst with ⟨Γ₁, hΓ₁, d₁⟩
  rcases htr with ⟨Γ₂, hΓ₂, d₂⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with h | h
    · exact hΓ₁ ξ h
    · exact hΓ₂ ξ h
  · exact ExtDerivation.eqTrans
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inl hξ)) d₁)
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inr hξ)) d₂)

theorem provable_eq_app {T : ClosedTheorySet Const} {σ τ : Ty Base}
    {f g : ClosedTerm Const (σ ⇒ τ)} (a : ClosedTerm Const σ)
    (h : Provable (Const := Const) T (.eq f g)) :
    Provable (Const := Const) T (.eq (.app f a) (.app g a)) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqApp a d⟩

theorem provable_eq_appArg {T : ClosedTheorySet Const} {σ τ : Ty Base}
    (f : ClosedTerm Const (σ ⇒ τ)) {s t : ClosedTerm Const σ}
    (h : Provable (Const := Const) T (.eq s t)) :
    Provable (Const := Const) T (.eq (.app f s) (.app f t)) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqAppArg f d⟩

theorem provable_eq_funext {T : ClosedTheorySet Const} {σ τ : Ty Base}
    {f g : ClosedTerm Const (σ ⇒ τ)}
    (h : Provable (Const := Const) T
      (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                 (.app (weaken (Base := Base) (σ := σ) g) (.var .vz))))) :
    Provable (Const := Const) T (.eq f g) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.funExt d⟩

/-! ## World-level equality bridges -/

theorem World.eq_refl_mem {W : ClosedTheorySet.World Const} {τ : Ty Base} (t : ClosedTerm Const τ) :
    (.eq t t : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W) (provable_eq_refl (Const := Const) W.carrier t)

theorem World.eq_symm_mem {W : ClosedTheorySet.World Const} {τ : Ty Base} {s t : ClosedTerm Const τ}
    (h : (.eq s t : ClosedFormula Const) ∈ W.carrier) :
    (.eq t s : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W) (provable_eq_symm (provable_of_mem (Const := Const) h))

theorem World.eq_trans_mem {W : ClosedTheorySet.World Const} {τ : Ty Base}
    {s t r : ClosedTerm Const τ}
    (hst : (.eq s t : ClosedFormula Const) ∈ W.carrier)
    (htr : (.eq t r : ClosedFormula Const) ∈ W.carrier) :
    (.eq s r : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W)
    (provable_eq_trans (provable_of_mem (Const := Const) hst) (provable_of_mem (Const := Const) htr))

theorem World.eq_app_mem {W : ClosedTheorySet.World Const} {σ τ : Ty Base}
    {f g : ClosedTerm Const (σ ⇒ τ)} (a : ClosedTerm Const σ)
    (h : (.eq f g : ClosedFormula Const) ∈ W.carrier) :
    (.eq (.app f a) (.app g a) : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W) (provable_eq_app a (provable_of_mem (Const := Const) h))

theorem World.eq_appArg_mem {W : ClosedTheorySet.World Const} {σ τ : Ty Base}
    (f : ClosedTerm Const (σ ⇒ τ)) {s t : ClosedTerm Const σ}
    (h : (.eq s t : ClosedFormula Const) ∈ W.carrier) :
    (.eq (.app f s) (.app f t) : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W) (provable_eq_appArg f (provable_of_mem (Const := Const) h))

theorem World.eq_funext_mem {W : ClosedTheorySet.World Const} {σ τ : Ty Base}
    {f g : ClosedTerm Const (σ ⇒ τ)}
    (h : (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                    (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))
          : ClosedFormula Const) ∈ W.carrier) :
    (.eq f g : ClosedFormula Const) ∈ W.carrier :=
  World.mem_of_provable (W := W) (provable_eq_funext (provable_of_mem (Const := Const) h))

end ClosedTheorySet
end Mettapedia.Logic.HOL
