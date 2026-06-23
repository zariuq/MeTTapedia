import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzOperations

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

namespace EtaleSpace.BasicTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

/--
Interpret a full HOL context by iterated fiber products over the base space.

This is the higher-order generalization of the already-live simple-type context
construction, but it only assumes a semantic carrier for every type.
-/
def ctxSpace (I : EtaleSpace.BasicTopologicalInterpretation Base Const X) :
    Ctx Base → EtaleSpace X
  | [] => EtaleSpace.terminal X
  | τ :: Γ => EtaleSpace.prod (I.space τ) (I.ctxSpace Γ)

@[simp] theorem ctxSpace_nil (I : EtaleSpace.BasicTopologicalInterpretation Base Const X) :
    I.ctxSpace [] = EtaleSpace.terminal X :=
  rfl

@[simp] theorem ctxSpace_cons (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (τ : Ty Base) (Γ : Ctx Base) :
    I.ctxSpace (τ :: Γ) = EtaleSpace.prod (I.space τ) (I.ctxSpace Γ) :=
  rfl

/--
A context morphism is a continuous map over the base space between interpreted
full HOL contexts.
-/
structure CtxHom
    (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (Γ Δ : Ctx Base) where
  toContinuousMap : C((I.ctxSpace Γ).Carrier, (I.ctxSpace Δ).Carrier)
  proj_comp : (I.ctxSpace Δ).proj ∘ toContinuousMap = (I.ctxSpace Γ).proj

/--
A term in context `Γ` and type `τ` is a continuous map over the base space from
the interpreted context into the interpreted type.
-/
structure CtxTerm
    (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (Γ : Ctx Base) (τ : Ty Base) where
  toContinuousMap : C((I.ctxSpace Γ).Carrier, (I.space τ).Carrier)
  proj_comp : (I.space τ).proj ∘ toContinuousMap = (I.ctxSpace Γ).proj

namespace CtxHom

variable {I : EtaleSpace.BasicTopologicalInterpretation Base Const X}
variable {Γ Δ Ξ Ω : Ctx Base}

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
def id (I : EtaleSpace.BasicTopologicalInterpretation Base Const X) (Γ : Ctx Base) :
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

@[simp] theorem id_apply (Γ : Ctx Base) (x : (I.ctxSpace Γ).Carrier) :
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
def terminal (I : EtaleSpace.BasicTopologicalInterpretation Base Const X) (Γ : Ctx Base) :
    I.CtxHom Γ [] where
  toContinuousMap := EtaleSpace.projMap (I.ctxSpace Γ)
  proj_comp := by
    funext x
    rfl

/-- Forget the head variable of a nonempty context. -/
def tail (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (τ : Ty Base) (Γ : Ctx Base) :
    I.CtxHom (τ :: Γ) Γ where
  toContinuousMap := EtaleSpace.prodSnd (I.space τ) (I.ctxSpace Γ)
  proj_comp := by
    funext x
    exact
      ((EtaleSpace.prod_proj_fst (I.space τ) (I.ctxSpace Γ) x).trans
        (EtaleSpace.prod_proj_snd (I.space τ) (I.ctxSpace Γ) x)).symm

end CtxHom

namespace CtxTerm

variable {I : EtaleSpace.BasicTopologicalInterpretation Base Const X}
variable {Γ Δ Ξ : Ctx Base} {τ υ : Ty Base}

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

/-- Weaken a term by extending the context with a new head variable. -/
def weaken (t : I.CtxTerm Γ τ) (υ : Ty Base) : I.CtxTerm (υ :: Γ) τ :=
  t.reindex (CtxHom.tail I υ Γ)

@[simp] theorem weaken_def (t : I.CtxTerm Γ τ) (υ : Ty Base) :
    t.weaken υ = t.reindex (CtxHom.tail I υ Γ) :=
  rfl

/-- A constant interpreted as a term in any context. -/
def const (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (Γ : Ctx Base) {τ : Ty Base} (c : Const τ) :
    I.CtxTerm Γ τ where
  toContinuousMap := (I.const c).toContinuousMap.comp (EtaleSpace.projMap (I.ctxSpace Γ))
  proj_comp := by
    funext x
    simpa [EtaleSpace.projMap, Function.comp] using
      congrFun (I.const c).proj_comp ((EtaleSpace.projMap (I.ctxSpace Γ)) x)

/-- The head variable of a nonempty context. -/
def head (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (τ : Ty Base) (Γ : Ctx Base) :
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

@[simp] theorem const_reindex (Γ : Ctx Base) (t : I.CtxHom Δ Γ)
    {τ : Ty Base} (c : Const τ) :
    (const I Γ c).reindex t = const I Δ c := by
  ext x
  have ht := congrFun t.proj_comp x
  simpa [const, EtaleSpace.projMap] using
    congrArg (I.const c).toContinuousMap ht

end CtxTerm

namespace CtxHom

variable {I : EtaleSpace.BasicTopologicalInterpretation Base Const X}
variable {Γ Δ : Ctx Base} {τ : Ty Base}

/-- Lift a context morphism under one additional bound variable. -/
def lift (σ : I.CtxHom Δ Γ) : I.CtxHom (τ :: Δ) (τ :: Γ) :=
  CtxTerm.cons (CtxTerm.head I τ Δ) ((CtxHom.tail I τ Δ).comp σ)

@[simp] theorem lift_tail (σ : I.CtxHom Δ Γ) :
    (lift (I := I) (τ := τ) σ).comp (CtxHom.tail I τ Γ) =
      (CtxHom.tail I τ Δ).comp σ := by
  rfl

/--
The generic head variable together with tail projection reconstructs the
identity on an extended full HOL context.
-/
@[simp] theorem cons_head_tail
    (τ : Ty Base) (Γ : Ctx Base) :
    CtxTerm.cons (CtxTerm.head I τ Γ) (CtxHom.tail I τ Γ) = CtxHom.id I (τ :: Γ) := by
  ext x
  apply Subtype.ext
  apply Prod.ext <;> rfl

/--
Any context morphism into an extended context is determined by its head term and
tail context morphism.
-/
@[simp] theorem cons_reconstruct (σ : I.CtxHom Γ (τ :: Δ)) :
    CtxTerm.cons ((CtxTerm.head I τ Δ).reindex σ) (σ.comp (CtxHom.tail I τ Δ)) = σ := by
  ext x
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- Every morphism into the empty full HOL context is terminal. -/
theorem toEmpty_eq_terminal (σ : I.CtxHom Γ []) :
    σ = terminal I Γ := by
  ext x
  change (EtaleSpace.terminal X).proj (σ.toContinuousMap x) = (I.ctxSpace Γ).proj x
  exact congrFun σ.proj_comp x

/--
Morphisms into an extended full HOL context are equivalently a head term and a
tail morphism.
-/
def splitEquiv (I : EtaleSpace.BasicTopologicalInterpretation Base Const X)
    (Γ : Ctx Base) (τ : Ty Base) (Δ : Ctx Base) :
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

end EtaleSpace.BasicTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
