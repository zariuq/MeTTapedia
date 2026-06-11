import Mettapedia.Logic.HOL.WorldEquality

/-!
# The canonical term-model domains

Over a world `M`, the canonical Henkin term model has, at each type `τ`, the domain
of closed terms quotiented by the world's equality predicate
`s ≡_τ t :⟺ (.eq s t) ∈ M.carrier`.  This is an equivalence (the world is closed
under `eqRefl/eqSymm/eqTrans`), and application descends to the quotient (closed
under `eqApp`/`eqAppArg`).  This `TermDom`/`appQ` pair is the applicative skeleton
of the model; the `HenkinModel` wrapper is built on top of it.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- The world's equality predicate on closed terms of a fixed type. -/
def termRel (M : World Const) {τ : Ty Base} (s t : ClosedTerm Const τ) : Prop :=
  (.eq s t : ClosedFormula Const) ∈ M.carrier

/-- Closed terms of type `τ` form a setoid under the world's equality. -/
def termSetoid (M : World Const) (τ : Ty Base) : Setoid (ClosedTerm Const τ) where
  r := termRel M
  iseqv :=
    ⟨fun t => World.eq_refl_mem t,
     fun h => World.eq_symm_mem h,
     fun h₁ h₂ => World.eq_trans_mem h₁ h₂⟩

/-- The canonical domain at type `τ`: closed terms mod provable equality in `M`. -/
def TermDom (M : World Const) (τ : Ty Base) : Type (max u v) :=
  Quotient (termSetoid M τ)

/-- The class of a closed term. -/
def TermDom.mk (M : World Const) {τ : Ty Base} (t : ClosedTerm Const τ) : TermDom M τ :=
  Quotient.mk (termSetoid M τ) t

theorem TermDom.mk_eq {M : World Const} {τ : Ty Base} {s t : ClosedTerm Const τ} :
    TermDom.mk M s = TermDom.mk M t ↔ (.eq s t : ClosedFormula Const) ∈ M.carrier :=
  Quotient.eq

/-- Application descends to the quotient domains. -/
def appQ (M : World Const) {σ τ : Ty Base}
    (f : TermDom M (σ ⇒ τ)) (a : TermDom M σ) : TermDom M τ :=
  Quotient.liftOn₂ f a (fun f a => TermDom.mk M (.app f a))
    (by
      intro f a f' a' hf ha
      apply Quotient.sound
      exact World.eq_trans_mem (World.eq_app_mem a hf) (World.eq_appArg_mem f' ha))

@[simp] theorem appQ_mk (M : World Const) {σ τ : Ty Base}
    (f : ClosedTerm Const (σ ⇒ τ)) (a : ClosedTerm Const σ) :
    appQ M (TermDom.mk M f) (TermDom.mk M a) = TermDom.mk M (.app f a) :=
  rfl

end ClosedTheorySet
end Mettapedia.Logic.HOL
