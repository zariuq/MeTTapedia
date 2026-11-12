import Mettapedia.GSLT.Core.ContextualLadder

/-!
# Retained typed values under context refinement

A view records a source typing and a requested typing in a category with
families. It is licensed at a substitution where those types coincide.
Transport uses that equality explicitly and commutes with further
substitution. Equality here is the equality of the chosen model; no
reflection into another calculus's conversion relation is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualTypedPublication

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

structure View (C : Cwf.{u, v, w, w'}) (context : C.Ctx) where
  declared : C.Ty context
  value : C.Tm context declared
  requested : C.Ty context

namespace View

variable {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx} (view : View C Γ)

def At (substitution : C.Sub Δ Γ) : Prop :=
  C.tySub view.declared substitution = C.tySub view.requested substitution

def realize (substitution : C.Sub Δ Γ) (licensed : view.At substitution) :
    C.Tm Δ (C.tySub view.requested substitution) :=
  cast (congrArg (C.Tm Δ) licensed) (C.tmSub view.value substitution)

def readout (substitution : C.Sub Δ Γ) (licensed : view.At substitution) :
    Σ type : C.Ty Δ, C.Tm Δ type :=
  ⟨C.tySub view.requested substitution, view.realize substitution licensed⟩

theorem readout_eq_substituted_value (substitution : C.Sub Δ Γ) (licensed : view.At substitution) :
    view.readout substitution licensed =
      (⟨C.tySub view.declared substitution, C.tmSub view.value substitution⟩ : Σ type : C.Ty Δ, C.Tm Δ type) :=
  Sigma.ext licensed.symm (cast_heq _ _)

def reindex (substitution : C.Sub Δ Γ) : View C Δ :=
  ⟨C.tySub view.declared substitution, C.tmSub view.value substitution,
    C.tySub view.requested substitution⟩

theorem at_reindex_iff (first : C.Sub Δ Γ) (second : C.Sub Θ Δ) :
    (view.reindex first).At second ↔ view.At (C.compS first second) := by
  unfold At reindex
  rw [C.tySub_comp, C.tySub_comp]

theorem at_precompose {first : C.Sub Δ Γ} (licensed : view.At first) (second : C.Sub Θ Δ) :
    view.At (C.compS first second) := by
  unfold At at licensed ⊢
  rw [C.tySub_comp, C.tySub_comp, licensed]

/-- Successive checking and realization is the same typed value as checking
and realizing along the composite substitution. -/
theorem readout_reindex (first : C.Sub Δ Γ) (second : C.Sub Θ Δ)
    (licensed : (view.reindex first).At second) :
    (view.reindex first).readout second licensed =
      view.readout (C.compS first second) ((view.at_reindex_iff first second).mp licensed) := by
  rw [(view.reindex first).readout_eq_substituted_value, view.readout_eq_substituted_value]
  apply Sigma.ext (C.tySub_comp view.declared first second).symm
  dsimp only [reindex]
  rw [C.tmSub_comp]
  exact (cast_heq _ _).symm

end View

end Mettapedia.TypeTheory.ContextualTypedPublication

#print axioms Mettapedia.TypeTheory.ContextualTypedPublication.View.readout_reindex
