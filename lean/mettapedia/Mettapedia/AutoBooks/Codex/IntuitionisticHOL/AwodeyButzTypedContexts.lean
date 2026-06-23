import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTypedFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

/--
A context morphism is a continuous map over the base space between interpreted
contexts.
-/
structure CtxHom
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ Δ : List (SimpleTy Base)) where
  toContinuousMap : C((I.ctxSpace Γ).Carrier, (I.ctxSpace Δ).Carrier)
  proj_comp : (I.ctxSpace Δ).proj ∘ toContinuousMap = (I.ctxSpace Γ).proj

/--
A term in context `Γ` and type `τ` is a continuous map over the base space from
the interpreted context into the interpreted type.
-/
structure CtxTerm
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) (τ : SimpleTy Base) where
  toContinuousMap : C((I.ctxSpace Γ).Carrier, (I.space τ).Carrier)
  proj_comp : (I.space τ).proj ∘ toContinuousMap = (I.ctxSpace Γ).proj

namespace CtxHom

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ Ξ Ω : List (SimpleTy Base)}

@[ext] theorem ext (σ ρ : I.CtxHom Γ Δ)
    (h : ∀ x, σ.toContinuousMap x = ρ.toContinuousMap x) : σ = ρ := by
  cases σ with
  | mk f hf =>
    cases ρ with
    | mk g hg =>
      simp only at h
      have hfg : f = g := by
        ext x
        exact h x
      subst hfg
      simp

/-- Identity context morphism. -/
def id (I : SimpleTopologicalInterpretation Base Const X) (Γ : List (SimpleTy Base)) :
    I.CtxHom Γ Γ where
  toContinuousMap := ContinuousMap.id _
  proj_comp := by
    funext x
    rfl

/-- Composition of context morphisms. -/
def comp (σ : I.CtxHom Γ Δ) (ρ : I.CtxHom Δ Ξ) : I.CtxHom Γ Ξ where
  toContinuousMap := ρ.toContinuousMap.comp σ.toContinuousMap
  proj_comp := by
    funext x
    exact (congrFun ρ.proj_comp (σ.toContinuousMap x)).trans (congrFun σ.proj_comp x)

@[simp] theorem id_apply (Γ : List (SimpleTy Base)) (x : (I.ctxSpace Γ).Carrier) :
    (id I Γ).toContinuousMap x = x :=
  rfl

@[simp] theorem comp_apply (σ : I.CtxHom Γ Δ) (ρ : I.CtxHom Δ Ξ)
    (x : (I.ctxSpace Γ).Carrier) :
    (σ.comp ρ).toContinuousMap x = ρ.toContinuousMap (σ.toContinuousMap x) :=
  rfl

@[simp] theorem id_comp (σ : I.CtxHom Γ Δ) :
    (id I Γ).comp σ = σ := by
  ext x
  rfl

@[simp] theorem comp_id (σ : I.CtxHom Γ Δ) :
    σ.comp (id I Δ) = σ := by
  ext x
  rfl

@[simp] theorem comp_assoc (σ : I.CtxHom Γ Δ) (ρ : I.CtxHom Δ Ξ)
    (θ : I.CtxHom Ξ Ω) :
    (σ.comp ρ).comp θ = σ.comp (ρ.comp θ) := by
  ext x
  rfl

/-- The unique context morphism into the empty context. -/
def terminal (I : SimpleTopologicalInterpretation Base Const X) (Γ : List (SimpleTy Base)) :
    I.CtxHom Γ [] where
  toContinuousMap := EtaleSpace.projMap (I.ctxSpace Γ)
  proj_comp := by
    funext x
    rfl

/-- Forget the head variable of a nonempty context. -/
def tail (I : SimpleTopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    I.CtxHom (τ :: Γ) Γ where
  toContinuousMap := EtaleSpace.prodSnd (I.space τ) (I.ctxSpace Γ)
  proj_comp := by
    funext x
    exact
      ((EtaleSpace.prod_proj_fst (I.space τ) (I.ctxSpace Γ) x).trans
        (EtaleSpace.prod_proj_snd (I.space τ) (I.ctxSpace Γ) x)).symm

end CtxHom

namespace CtxTerm

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ Ξ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

@[ext] theorem ext (s t : I.CtxTerm Γ τ)
    (h : ∀ x, s.toContinuousMap x = t.toContinuousMap x) : s = t := by
  cases s with
  | mk f hf =>
    cases t with
    | mk g hg =>
      simp only at h
      have hfg : f = g := by
        ext x
        exact h x
      subst hfg
      simp

/-- Reindex a term along a context morphism. -/
def reindex (t : I.CtxTerm Δ τ) (σ : I.CtxHom Γ Δ) : I.CtxTerm Γ τ where
  toContinuousMap := t.toContinuousMap.comp σ.toContinuousMap
  proj_comp := by
    funext x
    exact (congrFun t.proj_comp (σ.toContinuousMap x)).trans (congrFun σ.proj_comp x)

@[simp] theorem reindex_apply (t : I.CtxTerm Δ τ) (σ : I.CtxHom Γ Δ)
    (x : (I.ctxSpace Γ).Carrier) :
    (t.reindex σ).toContinuousMap x = t.toContinuousMap (σ.toContinuousMap x) :=
  rfl

@[simp] theorem reindex_id (t : I.CtxTerm Γ τ) :
    t.reindex (CtxHom.id I Γ) = t := by
  ext x
  rfl

@[simp] theorem reindex_comp (t : I.CtxTerm Ξ τ) (σ : I.CtxHom Γ Δ) (ρ : I.CtxHom Δ Ξ) :
    (t.reindex ρ).reindex σ = t.reindex (σ.comp ρ) := by
  ext x
  rfl

/-- A constant interpreted as a term in any context. -/
def const (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) (τ : SimpleTy Base) (c : Const τ.toTy) :
    I.CtxTerm Γ τ where
  toContinuousMap := (I.constSection τ c).toContinuousMap.comp (EtaleSpace.projMap (I.ctxSpace Γ))
  proj_comp := by
    funext x
    simpa [EtaleSpace.projMap, Function.comp] using
      congrFun (I.constSection τ c).proj_comp ((EtaleSpace.projMap (I.ctxSpace Γ)) x)

/-- The head variable of a nonempty context. -/
def head (I : SimpleTopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    I.CtxTerm (τ :: Γ) τ where
  toContinuousMap := EtaleSpace.prodFst (I.space τ) (I.ctxSpace Γ)
  proj_comp := by
    funext x
    exact (EtaleSpace.prod_proj_fst (I.space τ) (I.ctxSpace Γ) x).symm

/-- Extend a substitution by a new head term. -/
def cons (t : I.CtxTerm Γ τ) (σ : I.CtxHom Γ Δ) : I.CtxHom Γ (τ :: Δ) where
  toContinuousMap :=
    { toFun := fun x =>
        ⟨(t.toContinuousMap x, σ.toContinuousMap x), by
          have ht := congrFun t.proj_comp x
          have hσ := congrFun σ.proj_comp x
          exact ht.trans hσ.symm⟩
      continuous_toFun :=
        (t.toContinuousMap.continuous.prodMk σ.toContinuousMap.continuous).subtype_mk fun x => by
          have ht := congrFun t.proj_comp x
          have hσ := congrFun σ.proj_comp x
          exact ht.trans hσ.symm }
  proj_comp := by
    funext x
    exact congrFun t.proj_comp x

@[simp] theorem head_reindex_cons (t : I.CtxTerm Γ τ) (σ : I.CtxHom Γ Δ) :
    (head I τ Δ).reindex (cons t σ) = t := by
  ext x
  rfl

@[simp] theorem tail_cons (t : I.CtxTerm Γ τ) (σ : I.CtxHom Γ Δ) :
    (cons t σ).comp (CtxHom.tail I τ Δ) = σ := by
  ext x
  rfl

@[simp] theorem const_reindex (Γ : List (SimpleTy Base)) (t : I.CtxHom Δ Γ)
    (τ : SimpleTy Base) (c : Const τ.toTy) :
    (const I Γ τ c).reindex t = const I Δ τ c := by
  ext x
  have ht := congrFun t.proj_comp x
  simpa [const, EtaleSpace.projMap] using
    congrArg (I.constSection τ c).toContinuousMap ht

end CtxTerm

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
