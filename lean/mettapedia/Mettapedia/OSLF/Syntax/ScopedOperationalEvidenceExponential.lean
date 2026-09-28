import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mettapedia.OSLF.Syntax.MultiBinderPresheaf
import Mettapedia.OSLF.Syntax.BindingContextExtensionComparison

/-!
# Scoped operational evidence as a contextual function

An individual firing under an ordered binder context is an element of a
presheaf at the extended context. The same datum is a contextual function
from the representable binder context to the evidence presheaf. This
comparison applies to arbitrary evidence presheaves, including models with
additional events; endpoint predicates are obtained only afterward.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

universe u
variable {S : Signature}

private abbrev CtxObj (A : BindingCloneAlgebra.Algebra.{u} S) :=
  ContextObject A.substitution.toClone

/-- Reindex a retained datum along the simultaneous substitution assembled
from binder-local arguments and ambient variables. -/
private def bodyToTensorNat (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CtxObj A) (scope : Ctx S)
    (F : Base A ⥤ Type u)
    (body : F.obj (Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone scope) context))) :
    (binders A scope ⊗ yoneda.obj context) ⟶ F where
  app stage := TypeCat.ofHom fun entry =>
    F.map (Quiver.Hom.op (pair A.substitution.toClone entry.1 entry.2)) body
  naturality first last substitution := by
    apply ConcreteCategory.hom_ext
    rintro ⟨arguments, ambient⟩
    change first.unop ⟶ ContextObject.ofList A.substitution.toClone scope
      at arguments
    change first.unop ⟶ context at ambient
    have pairNaturality :
        pair A.substitution.toClone
            (substitution.unop ≫ arguments) (substitution.unop ≫ ambient) =
          substitution.unop ≫
            pair A.substitution.toClone arguments ambient := by
      symm
      apply categorical_pair_unique A.substitution.toClone
        (substitution.unop ≫ arguments) (substitution.unop ≫ ambient)
      · rw [Category.assoc, categorical_pair_fst]
      · rw [Category.assoc, categorical_pair_snd]
    change F.map (Quiver.Hom.op
        (pair A.substitution.toClone
          (substitution.unop ≫ arguments)
          (substitution.unop ≫ ambient))) body =
      F.map substitution
        (F.map (Quiver.Hom.op
          (pair A.substitution.toClone arguments ambient)) body)
    rw [pairNaturality, op_comp, F.map_comp]
    rfl

/-- Read a contextual evidence function at the context where all local
binders are available, using the two canonical projections. -/
private def tensorNatToBody (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CtxObj A) (scope : Ctx S)
    (F : Base A ⥤ Type u)
    (function : (binders A scope ⊗ yoneda.obj context) ⟶ F) :
    F.obj (Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone scope) context)) :=
  function.app (Opposite.op (concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone scope) context))
    (fstProjection A.substitution.toClone _ _,
      sndProjection A.substitution.toClone _ _)

/-- A contextual function with arbitrary presheaf codomain is exactly one
datum under the whole binder context. The codomain may retain multiple
different firings at the same endpoints. -/
def scopedEvidenceEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CtxObj A) (scope : Ctx S)
    (F : Base A ⥤ Type u) :
    ((binders A scope).functorHom F).obj (Opposite.op context) ≃
      F.obj (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context)) :=
  (yonedaEquiv.symm).trans
    ((FunctorToTypes.functorHomEquiv (binders A scope)
      (yoneda.obj context) F).trans {
      toFun := tensorNatToBody A context scope F
      invFun := bodyToTensorNat A context scope F
      left_inv := by
        intro function
        apply NatTrans.ext
        funext stage
        apply ConcreteCategory.hom_ext
        rintro ⟨arguments, ambient⟩
        let input := ContextObject.ofList A.substitution.toClone scope
        let extended := concat A.substitution.toClone input context
        change stage.unop ⟶ input at arguments
        change stage.unop ⟶ context at ambient
        let combined := pair A.substitution.toClone arguments ambient
        let canonical : (binders A scope ⊗ yoneda.obj context).obj
            (Opposite.op extended) :=
          (fstProjection A.substitution.toClone input context,
            sndProjection A.substitution.toClone input context)
        have natural := function.naturality_apply
          (Quiver.Hom.op combined) canonical
        change function.app stage
            (combined ≫ fstProjection A.substitution.toClone input context,
              combined ≫ sndProjection A.substitution.toClone input context) =
          F.map (Quiver.Hom.op combined)
            (tensorNatToBody A context scope F function) at natural
        rw [categorical_pair_fst, categorical_pair_snd] at natural
        exact natural.symm
      right_inv := by
        intro body
        change (F.map (Quiver.Hom.op
          (pair A.substitution.toClone
            (fstProjection A.substitution.toClone _ _)
            (sndProjection A.substitution.toClone _ _)))) body = body
        have eta := categorical_pair_eta A.substitution.toClone
          (𝟙 (concat A.substitution.toClone
            (ContextObject.ofList A.substitution.toClone scope) context))
        simp only [Category.id_comp] at eta
        rw [eta]
        change (F.map (𝟙 _)) body = body
        rw [F.map_id]
        rfl
    })

/-- Evaluate a contextual evidence function at the generic binder variables
and the ambient projection. -/
theorem scopedEvidenceEquiv_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CtxObj A) (scope : Ctx S)
    (F : Base A ⥤ Type u)
    (function : ((binders A scope).functorHom F).obj
      (Opposite.op context)) :
    scopedEvidenceEquiv A context scope F function =
      (function.app (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context))
        (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)))
        (fstProjection A.substitution.toClone _ _) := by
  change tensorNatToBody A context scope F
      ((FunctorToTypes.functorHomEquiv (binders A scope)
        (yoneda.obj context) F) (yonedaEquiv.symm function)) = _
  change (function.app
      (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context))
      (Quiver.Hom.op (sndProjection A.substitution.toClone _ _) ≫ 𝟙 _))
      (fstProjection A.substitution.toClone _ _) = _
  rw [Category.comp_id]

/-- Categorical reindexing of a scoped evidence function agrees with
reindexing its actual evidence under the binder-preserving context map. -/
theorem scopedEvidenceEquiv_reindex
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (F : Base A ⥤ Type u)
    {first last : Base A} (f : first ⟶ last)
    (function : ((binders A scope).functorHom F).obj first) :
    scopedEvidenceEquiv A last.unop scope F
        (((binders A scope).functorHom F).map f function) =
      F.map (Quiver.Hom.op (extendScope A scope f.unop))
        (scopedEvidenceEquiv A first.unop scope F function) := by
  rw [scopedEvidenceEquiv_apply, scopedEvidenceEquiv_apply]
  let input := ContextObject.ofList A.substitution.toClone scope
  let extension := extendScope A scope f.unop
  have naturality := function.naturality
    (Quiver.Hom.op extension)
    (Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop))
  have pointwise := ConcreteCategory.congr_hom naturality
    (fstProjection A.substitution.toClone input first.unop)
  change
      (function.app (Opposite.op (concat A.substitution.toClone input last.unop))
        (Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop) ≫
          Quiver.Hom.op extension))
        (extension ≫ fstProjection A.substitution.toClone input first.unop) =
      F.map (Quiver.Hom.op extension)
        ((function.app (Opposite.op
          (concat A.substitution.toClone input first.unop))
          (Quiver.Hom.op
            (sndProjection A.substitution.toClone input first.unop)))
          (fstProjection A.substitution.toClone input first.unop))
      at pointwise
  have sndLaw :
      Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop) ≫
        Quiver.Hom.op extension =
      f ≫ Quiver.Hom.op
        (sndProjection A.substitution.toClone input last.unop) := by
    simpa only [op_comp, Quiver.Hom.op_unop] using
      congrArg Quiver.Hom.op (extendScope_snd A scope f.unop)
  rw [sndLaw, extendScope_fst] at pointwise
  exact pointwise

/-- Applying a natural observation to scoped evidence agrees with observing
the retained evidence at the binder-extended context. This applies to the
source and target maps as well as to maps between operational models. -/
theorem scopedEvidenceEquiv_map
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : CtxObj A) (scope : Ctx S)
    {F G : Base A ⥤ Type u} (observation : F ⟶ G)
    (function : ((binders A scope).functorHom F).obj
      (Opposite.op context)) :
    scopedEvidenceEquiv A context scope G
        (((FunctorToTypes.rightAdj (binders A scope)).map observation).app
          (Opposite.op context) function) =
      observation.app (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context))
        (scopedEvidenceEquiv A context scope F function) := by
  let mapped : ((binders A scope).functorHom G).obj (Opposite.op context) :=
    ((FunctorToTypes.rightAdj (binders A scope)).map observation).app
      (Opposite.op context) function
  change scopedEvidenceEquiv A context scope G mapped = _
  rw [scopedEvidenceEquiv_apply A context scope G mapped,
    scopedEvidenceEquiv_apply A context scope F function]
  rfl

/-- Extend each ambient context by the same ordered binder list and evaluate
an arbitrary evidence presheaf there. The action on maps fixes bound
variables and transports only the ambient environment. -/
def scopedEvidence (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (F : Base A ⥤ Type u) : Base A ⥤ Type u where
  obj X := F.obj (Opposite.op (concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone scope) X.unop))
  map f := F.map (Quiver.Hom.op (extendScope A scope f.unop))
  map_id X := by
    change F.map (Quiver.Hom.op (extendScope A scope (𝟙 X.unop))) = 𝟙 _
    rw [extendScope_id]
    exact F.map_id _
  map_comp f g := by
    change F.map (Quiver.Hom.op
        (extendScope A scope (g.unop ≫ f.unop))) =
      F.map (Quiver.Hom.op (extendScope A scope f.unop)) ≫
        F.map (Quiver.Hom.op (extendScope A scope g.unop))
    rw [extendScope_comp, op_comp]
    exact F.map_comp _ _

/-- The contextual-function representation is natural at every ambient
context, not only a pointwise equivalence. In particular this applies to
the complete proof-relevant event presheaf of any lawful model. -/
def scopedEvidenceIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (F : Base A ⥤ Type u) :
    ((binders A scope).functorHom F) ≅ scopedEvidence A scope F := by
  refine NatIso.ofComponents
    (fun context => (scopedEvidenceEquiv A context.unop scope F).toIso) ?_
  intro first last f
  apply ConcreteCategory.hom_ext
  intro function
  exact scopedEvidenceEquiv_reindex A scope F f function

/-- Extending contexts by a fixed binder list acts functorially on every
evidence presheaf and every natural map of evidence. -/
def scopedEvidenceFunctor (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) :
    (Base A ⥤ Type u) ⥤ (Base A ⥤ Type u) where
  obj F := scopedEvidence A scope F
  map {F G} observation := {
    app X := observation.app (Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone scope) X.unop))
    naturality X Y f := observation.naturality
      (Quiver.Hom.op (extendScope A scope f.unop)) }
  map_id F := by
    ext X value
    rfl
  map_comp f g := by
    ext X value
    rfl

/-- Contextual exponentiation by the representable binder context *is*
context extension, naturally in both ambient substitutions and the chosen
presheaf of data. This applies equally to programs and retained events. -/
def scopedEvidenceFunctorIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) :
    FunctorToTypes.rightAdj (binders A scope) ≅
      scopedEvidenceFunctor A scope := by
  refine NatIso.ofComponents
    (fun F => scopedEvidenceIso A scope F) ?_
  intro F G observation
  ext context function
  exact scopedEvidenceEquiv_map A context.unop scope observation function

/-- The universal comparison applied to an actual substitution-operational
model retains its complete event, including rule occurrence and premise tree. -/
noncomputable def modelScopedEventEquiv
    {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (Y : SubstitutionModel R A)
    (context : CtxObj A) (scope : Ctx S) :
    ((binders A scope).functorHom (modelEvents R Y)).obj
        (Opposite.op context) ≃
      (modelEvents R Y).obj (Opposite.op
        (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context)) :=
  scopedEvidenceEquiv A context scope (modelEvents R Y)

/-- In a lawful operational model, substituting an ambient environment
under a premise's binder context acts on its entire individual firing tree.
The categorical exponent reindexing and the model's substitution action
agree, rather than merely giving the same endpoint pair. -/
theorem modelScopedEvent_substitute
    {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (Y : SubstitutionModel R A)
    (scope : Ctx S) {Γ Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier Γ Δ)
    (function : ((binders A scope).functorHom (modelEvents R Y)).obj
      (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))) :
    modelScopedEventEquiv R A Y
        (ContextObject.ofList A.substitution.toClone Δ) scope
        (((binders A scope).functorHom (modelEvents R Y)).map
          (Quiver.Hom.op (MultiBinderPresheaf.environmentArrow A σ)) function) =
      mapModelEvent R Y
        (Quiver.Hom.op (MultiBinderPresheaf.environmentArrow A
          (A.substitution.liftEnvironment σ scope)))
        (modelScopedEventEquiv R A Y
          (ContextObject.ofList A.substitution.toClone Γ) scope function) := by
  change scopedEvidenceEquiv A
      (ContextObject.ofList A.substitution.toClone Δ) scope
        (modelEvents R Y) _ = _
  rw [scopedEvidenceEquiv_reindex]
  change ((modelEvents R Y).map
      (Quiver.Hom.op (extendScope A scope
        (MultiBinderPresheaf.environmentArrow A σ))))
      (scopedEvidenceEquiv A
        (ContextObject.ofList A.substitution.toClone Γ) scope
        (modelEvents R Y) function) = _
  rw [extendScope_environment]
  rfl

/-- A lawful map of operational models transports the whole scoped firing,
with its rule action and ordered premise evidence, before or after reading
the contextual function. -/
theorem modelScopedEvent_map
    {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (context : CtxObj A) (scope : Ctx S)
    (function : ((binders A scope).functorHom (modelEvents R Y)).obj
      (Opposite.op context)) :
    modelScopedEventEquiv R A Z context scope
        (((FunctorToTypes.rightAdj (binders A scope)).map
          (mapModelEvents R h)).app (Opposite.op context) function) =
      (mapModelEvents R h).app
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context))
        (modelScopedEventEquiv R A Y context scope function) :=
  scopedEvidenceEquiv_map A context scope (mapModelEvents R h) function

/-- The source of a scoped firing is the scoped function obtained by
applying the natural source endpoint map. The original firing remains
available on the left of this equation. -/
theorem modelScopedEvent_source
    {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (Y : SubstitutionModel R A)
    (context : CtxObj A) (scope : Ctx S)
    (function : ((binders A scope).functorHom (modelEvents R Y)).obj
      (Opposite.op context)) :
    scopedEvidenceEquiv A context scope (states A)
        (((FunctorToTypes.rightAdj (binders A scope)).map
          (modelSource R Y)).app (Opposite.op context) function) =
      (modelSource R Y).app
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context))
        (modelScopedEventEquiv R A Y context scope function) :=
  scopedEvidenceEquiv_map A context scope (modelSource R Y) function

/-- The corresponding target endpoint remains natural under every binder
context and every ambient substitution. -/
theorem modelScopedEvent_target
    {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (Y : SubstitutionModel R A)
    (context : CtxObj A) (scope : Ctx S)
    (function : ((binders A scope).functorHom (modelEvents R Y)).obj
      (Opposite.op context)) :
    scopedEvidenceEquiv A context scope (states A)
        (((FunctorToTypes.rightAdj (binders A scope)).map
          (modelTarget R Y)).app (Opposite.op context) function) =
      (modelTarget R Y).app
        (Opposite.op (concat A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone scope) context))
        (modelScopedEventEquiv R A Y context scope function) :=
  scopedEvidenceEquiv_map A context scope (modelTarget R Y) function

#print axioms scopedEvidenceEquiv
#print axioms scopedEvidenceEquiv_reindex
#print axioms scopedEvidenceEquiv_map
#print axioms scopedEvidenceIso
#print axioms scopedEvidenceFunctorIso
#print axioms modelScopedEventEquiv
#print axioms modelScopedEvent_substitute
#print axioms modelScopedEvent_map
#print axioms modelScopedEvent_source
#print axioms modelScopedEvent_target

end Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
