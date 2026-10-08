import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationsReadout
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafReadback

/-!
# Structural endpoint comparisons for native operational evidence

Parallel commutativity and unused private-name elimination hold on arbitrary
supplied equation classes. Their whole natural-arrow consequences compare
the operational COMM endpoints with independently assembled continuation
arrows. No raw representative is chosen as a natural function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalEquations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf

abbrev algebra := AuthoredClassified.algebra
abbrev Base := IntrinsicScopedConditionalPresheaf.Base algebra
abbrev Ambient := CategoricalOperations.Ambient algebra
abbrev names := CategoricalOperations.names algebra
abbrev processes := CategoricalOperations.processes algebra

attribute [local irreducible] BindingEquationQuotientModel.operation

theorem parallel_classes (context : Ctx sig)
    (first second : algebra.substitution.Carrier context .pr) :
    algebra.operation Op.par (.cons first (.cons second .nil)) =
      algebra.operation Op.par (.cons second (.cons first .nil)) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      exact (AuthoredClassified.projection.raw.map_operation Op.par
        (.cons first (.cons second .nil))).symm.trans
          ((Quotient.sound (AuthoredEquations.structuralEq_complete
            (StructuralEq.parComm first second))).trans
            (AuthoredClassified.projection.raw.map_operation Op.par
              (.cons second (.cons first .nil))))

theorem fresh_weaken_class (context : Ctx sig)
    (process : algebra.substitution.Carrier context .pr) :
    algebra.operation Op.nu
      (.cons (algebra.substitution.weaken (fresh := Srt.nm) process) .nil) = process := by
  rw [BindingEquationQuotientSubstitution.algebra_weaken_eq_renameQ]
  induction process using Quotient.inductionOn with
  | _ process =>
    exact (AuthoredClassified.projection.raw.map_operation Op.nu
      (.cons (weaken process) .nil)).symm.trans
      (Quotient.sound (AuthoredEquations.structuralEq_complete
        (StructuralEq.nuUnused process)))

theorem parallel_current (world : Base) (first second : processes.obj world) :
    (CategoricalOperations.parallel algebra).app world (first,second) =
      (CategoricalOperations.parallel algebra).app world (second,first) := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [CategoricalOperations.parallel_readout, CategoricalOperations.parallel_readout]
  exact parallel_classes world.unop.context _ _

/-- The actual fresh-name arrow eliminates a complete function that ignores
its name argument, over every future stage. -/
theorem fresh_constant_current (world : Base) (process : processes.obj world) :
    (CategoricalOperations.fresh algebra).app world
      ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        (fst processes names)).app world process) = process := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [CategoricalOperations.fresh_readout, CategoricalOperations.abstraction_body]
  change algebra.operation Op.nu
    (.cons (algebra.substitution.substitute
      (BindingSubstitutionAlgebra.fromPositions world.unop.context
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
          algebra.substitution.toClone
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
            algebra.substitution.toClone [Srt.nm]) world.unop))
      (programsAtEquiv algebra .pr world process)) .nil) = _
  rw [IntrinsicScopedOperationalPresheafReadback.fromPositions_snd]
  exact fresh_weaken_class world.unop.context _

/-- A genuinely independent whole process arrow can pass through private
allocation without acquiring an observable unused name. -/
theorem fresh_vacuous {Z : Ambient} (body : Z ⟶ processes) :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
      (fst Z names ≫ body) ≫ CategoricalOperations.fresh algebra = body := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  have constant :
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        (fst Z names ≫ body)).app world parameter =
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        (fst processes names)).app world (body.app world parameter) := by
    apply Functor.functorHom_ext
    intro future change
    apply ConcreteCategory.hom_ext
    intro argument
    change body.app future (Z.map change parameter) =
      processes.map change (body.app world parameter)
    exact body.naturality_apply change parameter
  change (CategoricalOperations.fresh algebra).app world _ = _
  exact (congrArg ((CategoricalOperations.fresh algebra).app world) constant).trans
    (fresh_constant_current world (body.app world parameter))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalEquations
