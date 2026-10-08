import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Complete primitive and function-section readouts

The real categorical primitive arrows recover the independently supplied
binding-clone operations at each context. Empty binder arguments retain their
original value, and the binary binder comparison retains both ordered name
coordinates. Evaluation and abstraction read the entire future function
section, rather than extracting only its current value.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open FreeBindingTerms

universe u

variable (A : BindingCloneAlgebra.Algebra.{u} sig)

theorem plainArgument_body (sort : Srt) (X : Base A) (value : (programs A sort).obj X) :
    scopedBodyEquiv A X.unop [] sort ((plainArgument A sort).app X value) =
      programsAtEquiv A sort X value := by
  have evaluated := IntrinsicScopedOperationalPresheafPrograms.eval_body_substitute
    A [] sort X PUnit.unit ((plainArgument A sort).app X value)
  change programsAtEquiv A sort X ((programs A sort).map (𝟙 X) value) =
    A.substitution.substitute (fun _ position => A.substitution.injectVar position)
      (scopedBodyEquiv A X.unop [] sort ((plainArgument A sort).app X value)) at evaluated
  rw [Functor.map_id_apply] at evaluated
  exact (evaluated.trans (A.substitution.substitute_identity _)).symm

theorem binaryContext_first (X : Base A) (first second : (names A).obj X) :
    (binaryContextIso A).hom.app X (first, second) (0 : Fin 2) = first (0 : Fin 1) := rfl

theorem binaryContext_second (X : Base A) (first second : (names A).obj X) :
    (binaryContextIso A).hom.app X (first, second) (1 : Fin 2) = second (0 : Fin 1) := rfl

def unaryBody (X : Base A) (body : (unaryBodies A).obj X) :=
  scopedBodyEquiv A X.unop [Srt.nm] Srt.pr body

def binaryBody (X : Base A) (body : (binaryBodies A).obj X) :=
  scopedBodyEquiv A X.unop [Srt.nm, Srt.nm] Srt.pr ((binaryBodyIso A).hom.app X body)

theorem empty_readout (X : Base A) (point : (𝟙_ (Ambient A)).obj X) :
    programsAtEquiv A Srt.pr X ((empty A).app X point) = A.operation Op.nil FamilyArgs.nil := rfl

theorem parallel_readout (X : Base A) (first second : (processes A).obj X) :
    programsAtEquiv A Srt.pr X ((parallel A).app X (first, second)) =
      A.operation Op.par (.cons (programsAtEquiv A Srt.pr X first)
        (.cons (programsAtEquiv A Srt.pr X second) .nil)) := by
  change A.operation Op.par
    (.cons (scopedBodyEquiv A X.unop [] Srt.pr ((plainArgument A Srt.pr).app X first))
      (.cons (scopedBodyEquiv A X.unop [] Srt.pr ((plainArgument A Srt.pr).app X second)) .nil)) = _
  rw [plainArgument_body, plainArgument_body]

theorem output_readout (X : Base A) (channel datum : (names A).obj X) :
    programsAtEquiv A Srt.pr X ((output A).app X (channel, datum)) =
      A.operation Op.out1 (.cons (programsAtEquiv A Srt.nm X channel)
        (.cons (programsAtEquiv A Srt.nm X datum) .nil)) := by
  change A.operation Op.out1
    (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X channel))
      (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X datum)) .nil)) = _
  rw [plainArgument_body, plainArgument_body]

theorem send_readout (X : Base A) (channel first second : (names A).obj X) :
    programsAtEquiv A Srt.pr X ((send A).app X (channel, first, second)) =
      A.operation Op.out2 (.cons (programsAtEquiv A Srt.nm X channel)
        (.cons (programsAtEquiv A Srt.nm X first)
          (.cons (programsAtEquiv A Srt.nm X second) .nil))) := by
  change A.operation Op.out2
    (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X channel))
      (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X first))
        (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X second)) .nil))) = _
  rw [plainArgument_body, plainArgument_body, plainArgument_body]

theorem input_readout (X : Base A) (channel : (names A).obj X) (body : (unaryBodies A).obj X) :
    programsAtEquiv A Srt.pr X ((input A).app X (channel, body)) =
      A.operation Op.inp1 (.cons (programsAtEquiv A Srt.nm X channel) (.cons (unaryBody A X body) .nil)) := by
  change A.operation Op.inp1
    (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X channel))
      (.cons (unaryBody A X body) .nil)) = _
  rw [plainArgument_body]

theorem receive_readout (X : Base A) (channel : (names A).obj X) (body : (binaryBodies A).obj X) :
    programsAtEquiv A Srt.pr X ((receive A).app X (channel, body)) =
      A.operation Op.inp2 (.cons (programsAtEquiv A Srt.nm X channel) (.cons (binaryBody A X body) .nil)) := by
  change A.operation Op.inp2
    (.cons (scopedBodyEquiv A X.unop [] Srt.nm ((plainArgument A Srt.nm).app X channel))
      (.cons (binaryBody A X body) .nil)) = _
  rw [plainArgument_body]

theorem fresh_readout (X : Base A) (body : (unaryBodies A).obj X) :
    programsAtEquiv A Srt.pr X ((fresh A).app X body) =
      A.operation Op.nu (.cons (unaryBody A X body) .nil) := rfl

theorem replication_readout (X : Base A) (value : (processes A).obj X) :
    programsAtEquiv A Srt.pr X ((replication A).app X value) =
      A.operation Op.rep (.cons (programsAtEquiv A Srt.pr X value) .nil) := by
  change A.operation Op.rep
    (.cons (scopedBodyEquiv A X.unop [] Srt.pr ((plainArgument A Srt.pr).app X value)) .nil) = _
  rw [plainArgument_body]

/-- Abstraction acts at every supplied future stage and input name. -/
theorem abstraction_future {Z : Ambient A} (body : Z ⊗ names A ⟶ processes A)
    (X Y : Base A) (change : X ⟶ Y) (parameter : Z.obj X) (name : (names A).obj Y) :
    ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction body).app X parameter).app Y
        change name = body.app Y (Z.map change parameter, name) := rfl

theorem evaluation_readout (X : Base A) (body : (unaryBodies A).obj X) (name : (names A).obj X) :
    (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.evaluation (names A) (processes A)).app X
        (body, name) = body.app X (𝟙 X) name := rfl

/-- The canonical unary decoder reads the real abstraction at the whole
extended context, with the ambient parameter restricted and the bound name
left as its original projection. -/
theorem abstraction_body {Z : Ambient A} (body : Z ⊗ names A ⟶ processes A)
    (X : Base A) (parameter : Z.obj X) :
    unaryBody A X ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction body).app X parameter) =
      programsAtEquiv A Srt.pr
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList A.substitution.toClone [Srt.nm]) X.unop))
        (body.app
          (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
            (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList A.substitution.toClone [Srt.nm]) X.unop))
          (Z.map (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            A.substitution.toClone _ _)) parameter,
            Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone _ _)) := by
  rw [unaryBody, scopedBodyEquiv_apply]
  rfl

/-- The binary exponential comparison reads the supplied function at every
future arrow, through the inverse of the complete context comparison. -/
theorem binaryBodyIso_future (X Y : Base A) (change : X ⟶ Y)
    (body : (binaryBodies A).obj X) (arguments : (binders A [Srt.nm, Srt.nm]).obj Y) :
    (((binaryBodyIso A).hom.app X body).app Y change) arguments =
      body.app Y change ((binaryContextIso A).inv.app Y arguments) := by
  have evaluated := ConcreteCategory.congr_hom (C := Type u)
    (NatTrans.congr_app
      (MonoidalClosed.id_tensor_pre_app_comp_ev (binaryContextIso A).inv (processes A)) Y)
    (show (binders A [Srt.nm, Srt.nm] ⊗ binaryBodies A).obj Y from
      (arguments, (binaryBodies A).map change body))
  change (((binaryBodyIso A).hom.app Y ((binaryBodies A).map change body)).app Y (𝟙 _)) arguments =
    (((binaryBodies A).map change body).app Y (𝟙 _)) ((binaryContextIso A).inv.app Y arguments) at evaluated
  have natural := (binaryBodyIso A).hom.naturality_apply change body
  have point := congrArg
    (fun function : ((binders A [Srt.nm, Srt.nm]).functorHom (programs A Srt.pr)).obj Y =>
      (function.app Y (𝟙 Y)) arguments) natural.symm
  change ((((binaryBodyIso A).hom.app X body).app Y (change ≫ 𝟙 _)) arguments) =
    (((binaryBodyIso A).hom.app Y ((binaryBodies A).map change body)).app Y (𝟙 _)) arguments at point
  change _ = (body.app Y (change ≫ 𝟙 _)) ((binaryContextIso A).inv.app Y arguments) at evaluated
  rw [Category.comp_id] at point evaluated
  exact point.trans evaluated

theorem binaryContext_inv_first (X : Base A) (arguments : (binders A [Srt.nm, Srt.nm]).obj X) :
    (((binaryContextIso A).inv.app X arguments).1) (0 : Fin 1) = arguments (0 : Fin 2) := rfl

theorem binaryContext_inv_second (X : Base A) (arguments : (binders A [Srt.nm, Srt.nm]).obj X) :
    (((binaryContextIso A).inv.app X arguments).2) (0 : Fin 1) = arguments (1 : Fin 2) := rfl

/-- Decoding a binary abstraction retains both received names in their
authored order and the complete ambient parameter. -/
theorem binary_abstraction_body {Z : Ambient A}
    (body : Z ⊗ (names A ⊗ names A) ⟶ processes A) (X : Base A) (parameter : Z.obj X) :
    binaryBody A X ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction body).app X parameter) =
      programsAtEquiv A Srt.pr
        (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList A.substitution.toClone [Srt.nm, Srt.nm]) X.unop))
        (body.app
          (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concat A.substitution.toClone
            (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList A.substitution.toClone [Srt.nm, Srt.nm]) X.unop))
          (Z.map (Quiver.Hom.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            A.substitution.toClone _ _)) parameter,
            (binaryContextIso A).inv.app _
              (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection A.substitution.toClone _ _))) := by
  rw [binaryBody, scopedBodyEquiv_apply, binaryBodyIso_future]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperations
