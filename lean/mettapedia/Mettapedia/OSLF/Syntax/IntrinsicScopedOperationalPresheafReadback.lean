import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafPrograms
import Mettapedia.OSLF.Syntax.CategoricalContextualEquationSoundness
import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid

/-!
# Pointwise interpretation of operational presheaf programs

Generalized elements of the categorical program model read back to the actual
binding clone, retaining the ordinary context and the ambient stage context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafReadback

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf
open MultiBinderPresheaf IntrinsicScopedOperationalPresheafPrograms

universe u
variable {S : Signature}

/-- Reading a stage element retains its entire ordinary and ambient scope. -/
def read (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt}
    (e : (model A).ElemOver Z Γ s) (X : Base A) (z : Z.obj X) :
    A.substitution.Carrier (Γ ++ X.unop.context) s :=
  (powerBodiesIso A Γ s).hom.app X (((model A).elemEquiv e).app X z)

/-- A categorical ordinary environment at a point is an actual clone environment. -/
def readEnv (A : BindingCloneAlgebra.Algebra.{u} S)
    {W : target A} {Γ : Ctx S} (ρ : (model A).Env W Γ)
    (X : Base A) (w : W.obj X) :
    Environment S A.substitution.Carrier Γ X.unop.context :=
  fun s v => programsAtEquiv A s X ((ρ s v).app X w)

/-- The clone stage with the ordinary variables placed in front. -/
def extendedStage (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (X : Base A) :
    Base A := Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone Γ) X.unop)

/-- Canonical ordinary projections alongside the reindexed ambient parameter. -/
def canonicalPoint (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} (Γ : Ctx S) (X : Base A) (z : Z.obj X) :
    ((model A).ctx Γ ⊗ Z).obj (extendedStage A Γ X) :=
  ((contextAtEquiv A Γ (extendedStage A Γ X)).symm
    (fstProjection A.substitution.toClone _ _),
      Z.map (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)) z)

/-- Stage variables read as the original clone's prefix variables. -/
theorem read_injectVar (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt} (v : Var Γ s)
    (X : Base A) (z : Z.obj X) :
    read A (((model A).stage Z).substitution.injectVar v) X z =
      A.substitution.injectVar (injPrefix (Γ := X.unop.context) Γ v) := by
  change (powerBodiesIso A Γ s).hom.app X
    ((curry A (fst (CategoricalBindingModel.contextOf (programs A) Γ) Z ≫
      CategoricalBindingModel.projectVar (programs A) v)).app X z) = _
  exact curry_projection_body A v X z

/-- Reading commutes with every actual ambient clone substitution. -/
theorem read_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt}
    (e : (model A).ElemOver Z Γ s) {X Y : Base A} (f : X ⟶ Y) (z : Z.obj X) :
    read A e Y (Z.map f z) =
      A.substitution.toClone.substitute (read A e X z) (extendScope A Γ f.unop) := by
  have naturality := ((model A).elemEquiv e).naturality_apply f z
  exact (congrArg ((powerBodiesIso A Γ s).hom.app Y) naturality).trans
    (scopedBodyEquiv_reindex A Γ s f (((model A).elemEquiv e).app X z))

private theorem elemEquiv_restage_app
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (M : CategoricalBindingModel.Model S (target A))
    {Z Z' : target A} {Γ : Ctx S} {s : S.Srt}
    (h : Z' ⟶ Z) (e : M.ElemOver Z Γ s) (X : Base A) (z : Z'.obj X) :
    (M.elemEquiv (M.restageElem h e)).app X z = (M.elemEquiv e).app X (h.app X z) :=
  congrArg (fun (g : Z' ⟶ M.power Γ s) => g.app X z) (M.elemEquiv_restage h e)

/-- Generalized restaging acts on the actual retained ambient parameter. -/
theorem read_restage (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z Z' : target A} {Γ : Ctx S} {s : S.Srt}
    (h : Z' ⟶ Z) (e : (model A).ElemOver Z Γ s) (X : Base A) (z : Z'.obj X) :
    read A ((model A).restageElem h e) X z = read A e X (h.app X z) := by
  exact congrArg ((powerBodiesIso A Γ s).hom.app X)
    (elemEquiv_restage_app (model A) h e X z)

/-- A stage element is read at its canonical ordinary and ambient projections. -/
theorem read_canonical (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ : Ctx S} {s : S.Srt}
    (e : (model A).ElemOver Z Γ s) (X : Base A) (z : Z.obj X) :
    read A e X z = programsAtEquiv A s (extendedStage A Γ X)
      ((e.value ((model A).ctx Γ ⊗ Z) (snd _ _) ((model A).genericEnv Γ Z)).app
        (extendedStage A Γ X) (canonicalPoint A Γ X z)) := by
  exact curry_body A ((model A).elemValue e) X z

theorem tupleEnv_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {W : target A} {Γ : Ctx S} (ρ : (model A).Env W Γ)
    (X : Base A) (w : W.obj X) :
    fromPositions Γ (contextAtEquiv A Γ X (((model A).tupleEnv ρ).app X w)) =
      readEnv A ρ X w := by
  funext s v
  have coordinate := congrArg
    (fun (k : W ⟶ programs A s) => programsAtEquiv A s X (k.app X w))
    ((model A).tupleEnv_projectVar ρ v)
  exact (context_projection A v X (((model A).tupleEnv ρ).app X w)).symm.trans coordinate

/-- Every generalized value evaluates by the original contextual substitution,
with its ordinary environment separate from its ambient stage variables. -/
theorem value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z W : target A} {Γ : Ctx S} {s : S.Srt}
    (e : (model A).ElemOver Z Γ s) (m : W ⟶ Z) (ρ : (model A).Env W Γ)
    (X : Base A) (w : W.obj X) :
    programsAtEquiv A s X ((e.value W m ρ).app X w) =
      A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment
          (readEnv A ρ X w) (fun _ v => A.substitution.injectVar v))
        (read A e X (m.app X w)) := by
  have eta := congrArg
    (fun (a : (model A).ElemOver Z Γ s) =>
      programsAtEquiv A s X ((a.value W m ρ).app X w))
    ((model A).elemEquiv.left_inv e)
  change programsAtEquiv A s X
      ((eval A Γ s).app X
        ((((model A).tupleEnv ρ).app X w),
          (((model A).elemEquiv e).app X (m.app X w)))) =
    programsAtEquiv A s X ((e.value W m ρ).app X w) at eta
  have evaluated := eval_body_substitute A Γ s X
    (((model A).tupleEnv ρ).app X w)
    (((model A).elemEquiv e).app X (m.app X w))
  exact eta.symm.trans (evaluated.trans
    (congrArg (fun env => A.substitution.substitute
      (SemanticContextualMetavariables.joinEnvironment env
        (fun _ v => A.substitution.injectVar v))
      (read A e X (m.app X w))) (tupleEnv_point A ρ X w)))

/-- A reindexed generalized value substitutes its ordinary environment and
the actual map of its ambient stage separately into the original body. -/
theorem value_reindexed_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z W : target A} {Γ : Ctx S} {s : S.Srt}
    (e : (model A).ElemOver Z Γ s) (m : W ⟶ Z) (ρ : (model A).Env W Γ)
    {X Y : Base A} (f : X ⟶ Y) (z : Z.obj X) (w : W.obj Y)
    (point : m.app Y w = Z.map f z) :
    programsAtEquiv A s Y ((e.value W m ρ).app Y w) =
      A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment
          (readEnv A ρ Y w) (fromPositions X.unop.context f.unop))
        (read A e X z) := by
  have reindexed := read_reindex A e f z
  change read A e Y (Z.map f z) =
    A.substitution.substitute
      (fromPositions (Γ ++ X.unop.context) (extendScope A Γ f.unop))
      (read A e X z) at reindexed
  have extended := fromPositions_extendScope A Γ f.unop
  have lifted := reindexed.trans
    (congrArg (fun env => A.substitution.substitute env (read A e X z)) extended)
  have evaluated := value_point A e m ρ Y w
  rw [point] at evaluated
  rw [lifted] at evaluated
  have composed :
      (fun t v => A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment
          (readEnv A ρ Y w) (fun _ v => A.substitution.injectVar v))
        (A.substitution.liftEnvironment (fromPositions X.unop.context f.unop) Γ t v)) =
      SemanticContextualMetavariables.joinEnvironment
        (readEnv A ρ Y w) (fromPositions X.unop.context f.unop) := by
    funext t v
    simpa only [A.substitution.substitute_identity] using
      IntrinsicScopedConditionalSubstitution.substitute_join_liftEnvironment A.substitution
        (fun _ v => A.substitution.injectVar v)
        (fromPositions X.unop.context f.unop) Γ (readEnv A ρ Y w) v
  exact evaluated.trans
    ((A.substitution.substitute_comp _ _ (read A e X z)).trans
      (congrArg (fun env => A.substitution.substitute env (read A e X z)) composed))

/-- The ambient context projection keeps every ambient variable after the
complete ordinary prefix. -/
theorem fromPositions_snd (A : BindingCloneAlgebra.Algebra.{u} S)
    (Δ : Ctx S) (X : Base A) :
    fromPositions X.unop.context
        (sndProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Δ) X.unop) =
      (fun _ v => A.substitution.injectVar (weakenVar Δ v)) := by
  have coordinates :
      sndProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone Δ) X.unop =
        (fun i => A.substitution.injectVar
          (weakenVar Δ (varOfIdx X.unop.context i))) := by
    funext i
    exact rightProjection_as_var A Δ X.unop.context i
  rw [coordinates]
  funext s v
  exact fromPositions_ofEnvironment
    (fun _ var => A.substitution.injectVar (weakenVar Δ var)) v

/-- Substitution of generalized elements reads as the original substitution
of their ordinary values, with ambient variables retained after the target prefix. -/
theorem read_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z : target A} {Γ Δ : Ctx S} {s : S.Srt}
    (σ : Environment S ((model A).stage Z).substitution.Carrier Γ Δ)
    (e : (model A).ElemOver Z Γ s) (X : Base A) (z : Z.obj X) :
    read A (((model A).stage Z).substitution.substitute σ e) X z =
      A.substitution.substitute
        (SemanticContextualMetavariables.joinEnvironment
          (fun t v => read A (σ t v) X z)
          (fun _ v => A.substitution.injectVar (weakenVar Δ v)))
        (read A e X z) := by
  let W : target A := (model A).ctx Δ ⊗ Z
  let Y : Base A := extendedStage A Δ X
  let f : X ⟶ Y := Quiver.Hom.op
    (sndProjection A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone Δ) X.unop)
  let p : W.obj Y := canonicalPoint A Δ X z
  let ρ : (model A).Env W Γ :=
    (model A).envValue σ W (snd _ _) ((model A).genericEnv Δ Z)
  have canonical := read_canonical A
    (((model A).stage Z).substitution.substitute σ e) X z
  change read A (((model A).stage Z).substitution.substitute σ e) X z =
    programsAtEquiv A s Y ((e.value W (snd _ _) ρ).app Y p) at canonical
  have evaluated := value_reindexed_point A e (snd _ _) ρ f z p rfl
  have ordinary : readEnv A ρ Y p = (fun t v => read A (σ t v) X z) := by
    funext t v
    exact (read_canonical A (σ t v) X z).symm
  have ambient : fromPositions X.unop.context f.unop =
      (fun _ v => A.substitution.injectVar (weakenVar Δ v)) :=
    fromPositions_snd A Δ X
  exact canonical.trans (evaluated.trans
    (congrArg (fun env => A.substitution.substitute env (read A e X z))
      (congrArg₂ SemanticContextualMetavariables.joinEnvironment ordinary ambient)))

private theorem variable_blocks :
    ∀ (bs : Ctx S) {Γ : Ctx S} {s : S.Srt} (v : Var (bs ++ Γ) s),
      (∃ w : Var bs s, v = injPrefix (Γ := Γ) bs w) ∨
        (∃ w : Var Γ s, v = weakenVar bs w)
  | [], _, _, v => .inr ⟨v, rfl⟩
  | _ :: bs, Γ, _, .zero => .inl ⟨.zero, rfl⟩
  | _ :: bs, Γ, _, .succ v => by
      rcases variable_blocks bs v with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · exact .inl ⟨.succ w, rfl⟩
      · exact .inr ⟨w, rfl⟩

private theorem injPrefix_withMetas {N : List (MetaArity S)} :
    ∀ (bs : Ctx S) {Γ : Ctx S} {s : S.Srt} (v : Var bs s),
      injPrefix (S := withMetas S N) (Γ := Γ) bs v = injPrefix (S := S) bs v
  | _, _, _, .zero => rfl
  | _ :: bs, _, _, .succ v => congrArg Var.succ (injPrefix_withMetas bs v)

/-- Ordinary environment values are natural under every ambient substitution. -/
theorem readEnv_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    {W : target A} {Γ : Ctx S} (ρ : (model A).Env W Γ)
    {X Y : Base A} (f : X ⟶ Y) (w : W.obj X) :
    readEnv A ρ Y (W.map f w) =
      (fun s v => A.substitution.substitute (fromPositions X.unop.context f.unop)
        (readEnv A ρ X w s v)) := by
  funext s v
  exact congrArg (programsAtEquiv A s Y) ((ρ s v).naturality_apply f w)

/-- Opening a binder context at its canonical projections agrees with the
original capture-avoiding environment lift. -/
theorem readEnv_extend_canonical (A : BindingCloneAlgebra.Algebra.{u} S)
    {W : target A} {Γ : Ctx S} (ρ : (model A).Env W Γ)
    (bs : Ctx S) (X : Base A) (w : W.obj X) :
    readEnv A ((model A).extendEnv bs ρ) (extendedStage A bs X)
        (canonicalPoint A bs X w) =
      A.substitution.liftEnvironment (readEnv A ρ X w) bs := by
  funext s v
  change programsAtEquiv A s (extendedStage A bs X)
    (((model A).extendEnv bs ρ s v).app (extendedStage A bs X)
      (canonicalPoint A bs X w)) = _
  rcases variable_blocks bs v with ⟨b, rfl⟩ | ⟨old, rfl⟩
  · have coordinate := (model A).extendEnv_injPrefix (N := []) bs ρ b
    rw [injPrefix_withMetas] at coordinate
    have evaluated := congrArg
      (fun (k : (model A).ctx bs ⊗ W ⟶ programs A s) =>
        programsAtEquiv A s (extendedStage A bs X)
          (k.app (extendedStage A bs X) (canonicalPoint A bs X w))) coordinate
    exact evaluated.trans ((context_projection_prefix A b X).trans
      (liftEnvironment_injPrefix A (readEnv A ρ X w) bs b).symm)
  · have coordinate := (model A).extendEnv_old bs ρ old
    have evaluated := congrArg
      (fun (k : (model A).ctx bs ⊗ W ⟶ programs A s) =>
        programsAtEquiv A s (extendedStage A bs X)
          (k.app (extendedStage A bs X) (canonicalPoint A bs X w))) coordinate
    have reindexed := congrFun (congrFun
      (readEnv_reindex A ρ
        (Quiver.Hom.op (sndProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone bs) X.unop)) w) s) old
    have ambient := fromPositions_snd A bs X
    exact evaluated.trans (reindexed.trans
      ((congrArg (fun env => A.substitution.substitute env (readEnv A ρ X w s old))
        ambient).trans
          (IntrinsicScopedConditionalSubstitution.liftEnvironment_weakenVar A.substitution
            (readEnv A ρ X w) bs old).symm))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafReadback
