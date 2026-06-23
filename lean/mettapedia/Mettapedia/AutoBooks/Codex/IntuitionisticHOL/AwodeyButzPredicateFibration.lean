import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzGenericPredicates

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace CtxHom

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Every morphism into the empty context is the terminal one. -/
theorem toEmpty_eq_terminal (σ : I.CtxHom Γ []) :
    σ = terminal I Γ := by
  ext x
  change (EtaleSpace.terminal X).proj (σ.toContinuousMap x) = (I.ctxSpace Γ).proj x
  exact congrFun σ.proj_comp x

/-- Morphisms into the empty context carry no extra information. -/
def toEmptyEquivPUnit (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) :
    I.CtxHom Γ [] ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => terminal I Γ
  left_inv := by
    intro σ
    exact (toEmpty_eq_terminal (I := I) σ).symm
  right_inv := by
    intro u
    cases u
    rfl

/--
Substitutions into an extended context are equivalently a head term together
with a tail substitution.
-/
def splitEquiv (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) (τ : SimpleTy Base) (Δ : List (SimpleTy Base)) :
    I.CtxHom Γ (τ :: Δ) ≃ (I.CtxTerm Γ τ × I.CtxHom Γ Δ) where
  toFun := fun σ => ((CtxTerm.head I τ Δ).reindex σ, σ.comp (tail I τ Δ))
  invFun := fun p => CtxTerm.cons p.1 p.2
  left_inv := by
    intro σ
    exact cons_reconstruct (I := I) (Γ := Γ) (Δ := Δ) (τ := τ) σ
  right_inv := by
    intro p
    rcases p with ⟨t, σ⟩
    apply Prod.ext
    · exact CtxTerm.head_reindex_cons (I := I) t σ
    · exact CtxTerm.tail_cons (I := I) t σ

end CtxHom

/--
Predicates in context are equivalently substitutions into the one-variable
proposition context.
-/
def predContextEquiv
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) :
    I.CtxHom Γ [.prop] ≃ I.Pred Γ where
  toFun := fun σ => (genericProp I []).reindex σ
  invFun := fun p => CtxTerm.cons p (CtxHom.terminal I Γ)
  left_inv := by
    intro σ
    calc
      CtxTerm.cons ((genericProp I []).reindex σ) (CtxHom.terminal I Γ)
          = CtxTerm.cons ((genericProp I []).reindex σ) (σ.comp (CtxHom.tail I .prop [])) := by
              rw [CtxHom.toEmpty_eq_terminal (I := I) (σ := σ.comp (CtxHom.tail I .prop []))]
      _ = σ := by
        simp [genericProp, genericVar]
  right_inv := by
    intro p
    exact CtxTerm.genericProp_reindex_cons (I := I) p (CtxHom.terminal I Γ)

@[simp] theorem predContextEquiv_apply
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) (σ : I.CtxHom Γ [.prop]) :
    predContextEquiv I Γ σ = (genericProp I []).reindex σ :=
  rfl

@[simp] theorem predContextEquiv_symm_apply
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) (p : I.Pred Γ) :
    (predContextEquiv I Γ).symm p = CtxTerm.cons p (CtxHom.terminal I Γ) :=
  rfl

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
