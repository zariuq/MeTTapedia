import Mettapedia.Logic.HOL.TermModel.Domain
import Mettapedia.Logic.HOL.Semantics.Henkin

/-!
# Realization relation for the canonical Henkin general model

Following the (refined) general-model construction: rather than quotient at arrow
types, we realize the **existing** `PreModel` interface — base-type carriers are the
closed-term quotients, arrow types are the ambient function space, and the Henkin
fragment is cut out by `adm = representability`.  This file sets up:

* the propositional-extensionality membership bridge `eqProp_mem_iff`
  (`(s = t) ∈ M → (s ∈ M ↔ t ∈ M)`), needed for the prop fiber;
* the base-type carrier `termCarrier`;
* the **type-indexed realization relation** `Rep M τ d t` ("the semantic element `d`
  is represented by the closed term `t`"), and `adm`.

The denotational model (`constDen` at arrow types) and the fundamental lemma are
built on top of these.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Propositional extensionality membership bridge -/

theorem provable_eqProp_mp {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (h : Provable (Const := Const) T (.eq φ ψ)) (hφ : Provable (Const := Const) T φ) :
    Provable (Const := Const) T ψ := by
  rcases h with ⟨Γ, hΓ, d⟩
  rcases hφ with ⟨Γ', hΓ', dφ⟩
  refine ⟨Γ ++ Γ', ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with h | h
    · exact hΓ ξ h
    · exact hΓ' ξ h
  · exact ExtDerivation.impE
      (ExtDerivation.eqPropEL (ExtDerivation.mono
        (by intro ξ hξ; exact List.mem_append.mpr (.inl hξ)) d))
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inr hξ)) dφ)

theorem World.eqProp_mp {W : World Const} {φ ψ : ClosedFormula Const}
    (h : (.eq φ ψ : ClosedFormula Const) ∈ W.carrier) (hφ : φ ∈ W.carrier) : ψ ∈ W.carrier :=
  World.mem_of_provable (W := W)
    (provable_eqProp_mp (provable_of_mem (Const := Const) h) (provable_of_mem (Const := Const) hφ))

/-- Propositional extensionality at the membership level: equal propositions are
co-members of the world. -/
theorem eqProp_mem_iff {W : World Const} {φ ψ : ClosedFormula Const}
    (h : (.eq φ ψ : ClosedFormula Const) ∈ W.carrier) : φ ∈ W.carrier ↔ ψ ∈ W.carrier :=
  ⟨fun hφ => World.eqProp_mp h hφ, fun hψ => World.eqProp_mp (World.eq_symm_mem h) hψ⟩

/-! ## The general-model carrier and the realization relation -/

/-- Base-type carrier of the canonical general model: closed terms mod provable
equality, lifted to the model universe. -/
abbrev termCarrier (M : World Const) (b : Base) : Type (max (u + 1) v) :=
  ULift.{u + 1} (TermDom M (Ty.base b))

/-- The realization relation `Rep M τ d t`: the semantic element `d : ⟦τ⟧` is
represented by the closed term `t`.  By recursion on the type: at `prop`, truth
matches membership; at base, identity of quotient classes; at arrows, application
preserves representation. -/
def Rep (M : World Const) :
    (τ : Ty Base) → Ty.denote (termCarrier M) τ → ClosedTerm Const τ → Prop
  | .prop, p, t => p.down ↔ (t ∈ M.carrier)
  | .base b, d, t => d = (ULift.up (TermDom.mk M t) : termCarrier M b)
  | .arr σ ρ, f, t =>
      ∀ (d : Ty.denote (termCarrier M) σ) (u : ClosedTerm Const σ),
        Rep M σ d u → Rep M ρ (f d) (.app t u)

/-- Admissibility = representability by a closed term. -/
def admissible (M : World Const) (τ : Ty Base) (d : Ty.denote (termCarrier M) τ) : Prop :=
  ∃ t : ClosedTerm Const τ, Rep M τ d t

end ClosedTheorySet
end Mettapedia.Logic.HOL
