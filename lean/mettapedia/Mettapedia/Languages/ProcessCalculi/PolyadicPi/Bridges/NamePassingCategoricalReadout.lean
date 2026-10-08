import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalContexts

/-!
# The full continuation-arrow and authored compiler comparison

The source meaning is independently assembled from actual communication,
product and exponential arrows. Its complete future function sections are
read against the authored open compiler. Context restriction, both received
binder positions and the stored value outside its reference binder are
retained by the comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation
open NamePassingContinuationOperations

theorem freshName_point (target : Ctx sig) :
    (rawPoint (.var .zero : Name (Srt.nm :: target))) =
      Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection algebra.substitution.toClone
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
          algebra.substitution.toClone [Srt.nm]) (stage target).unop := by
  apply (programsAtEquiv algebra Srt.nm (stage (Srt.nm :: target))).injective
  rfl

theorem meaning_substitution {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (assigned : Sub sig target future) :
    operations.termObject.map (rawChange assigned)
        ((meaning operations term).app (stage target) (contextPoint environment)) =
      (meaning operations term).app (stage future) (contextPoint (environment.substitute assigned)) :=
  ((meaning operations term).naturality_apply (rawChange assigned) (contextPoint environment)).symm.trans
    (congrArg ((meaning operations term).app (stage future)) (contextPoint_substitution environment assigned))

/-- The independent categorical function meaning, read at any future
substitution, agrees with that same arrow on the restricted environment. -/
theorem meaning_future {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (assigned : Sub sig target future) (result : Name future) :
    (((meaning operations term).app (stage target) (contextPoint environment)).app
        (stage future) (rawChange assigned)) (rawPoint result) =
      (((meaning operations term).app (stage future) (contextPoint (environment.substitute assigned))).app
        (stage future) (𝟙 _)) (rawPoint result) := by
  have point := congrArg
    (fun function : ((binders algebra [Srt.nm]).functorHom (programs algebra Srt.pr)).obj (stage future) =>
      (function.app (stage future) (𝟙 _)) (rawPoint result))
    (meaning_substitution term environment assigned)
  change (((meaning operations term).app (stage target) (contextPoint environment)).app
    (stage future) (rawChange assigned ≫ 𝟙 _)) (rawPoint result) = _ at point
  rw [Category.comp_id] at point
  exact point

/-- The whole contextual body of a source function is determined by its
actual return call at the canonical extended context. -/
theorem meaning_body {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target) :
    scopedBodyEquiv algebra (stage target).unop [Srt.nm] Srt.pr
        ((meaning operations term).app (stage target) (contextPoint environment)) =
      programsAtEquiv algebra Srt.pr (stage (Srt.nm :: target))
        ((((meaning operations term).app (stage (Srt.nm :: target))
          (contextPoint (environment.substitute weakening))).app
            (stage (Srt.nm :: target)) (𝟙 _)) (rawPoint (.var .zero))) := by
  have body := scopedBodyEquiv_apply algebra (stage target).unop [Srt.nm] Srt.pr
    ((meaning operations term).app (stage target) (contextPoint environment))
  have projection := rawChange_scopeWeakening target [Srt.nm]
  change rawChange (weakening (Δ := target)) = _ at projection
  rw [← projection] at body
  rw [← freshName_point] at body
  change scopedBodyEquiv algebra (stage target).unop [Srt.nm] Srt.pr
      ((meaning operations term).app (stage target) (contextPoint environment)) =
    programsAtEquiv algebra Srt.pr (stage (Srt.nm :: target))
      ((((meaning operations term).app (stage target) (contextPoint environment)).app
        (stage (Srt.nm :: target)) (rawChange weakening)) (rawPoint (.var .zero))) at body
  exact body.trans (congrArg (programsAtEquiv algebra Srt.pr (stage (Srt.nm :: target)))
    (meaning_future term environment weakening (.var .zero)))

theorem boundMeaning_future {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: context)) (environment : Environment context target)
    (assigned : Sub sig target future) (reference : Name future) :
    (((boundMeaning operations (meaning operations body)).app (stage target) (contextPoint environment)).app
        (stage future) (rawChange assigned)) (rawPoint reference) =
      (meaning operations body).app (stage future)
        (contextPoint (extendName (environment.substitute assigned) reference)) := by
  change (meaning operations body).app (stage future)
    (rawPoint reference, (contextValue operations context).map (rawChange assigned) (contextPoint environment)) = _
  exact congrArg (fun parameter => (meaning operations body).app (stage future) (rawPoint reference, parameter))
    (contextPoint_substitution environment assigned)

theorem reference_current {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (name : NamePassing.Presentation.Name context) (environment : Environment context target) (result : Name target) :
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations (NamePassing.Presentation.reference name)).app
          (stage target) (contextPoint environment)).app (stage target) (𝟙 _)) (rawPoint result)) =
      (Quotient.mk _ (out1 (interpretName name environment) result) : TermQ equations target .pr) := by
  simp only [NamePassing.Presentation.reference, meaning]
  dsimp only [Operations.reference]
  simp only [NatTrans.comp_app_apply]
  change programsAtEquiv algebra .pr (stage target)
    ((((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
      (CategoricalOperations.output algebra)).app (stage target)
        ((nameMeaning operations name).app (stage target) (contextPoint environment))).app
      (stage target) (𝟙 _)) (rawPoint result)) = _
  rw [CategoricalOperations.abstraction_future, Functor.map_id_apply]
  rw [nameMeaning_readout, CategoricalOperations.output_readout, rawPoint_readout, rawPoint_readout]
  exact (AuthoredClassified.projection.raw.map_operation Op.out1
    (.cons (interpretName name environment) (.cons result .nil))).symm

theorem carrier_shape {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (name : NamePassing.Presentation.Name context) (value body : NamePassing.Presentation.Program context)
    (environment : Environment context target) (result : Name target) :
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations (NamePassing.Presentation.carrier name value body)).app
          (stage target) (contextPoint environment)).app (stage target) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.par
        (.cons (programsAtEquiv algebra .pr (stage target)
          ((((meaning operations body).app (stage target) (contextPoint environment)).app
            (stage target) (𝟙 _)) (rawPoint result)))
          (.cons (algebra.operation Op.inp1
            (.cons (Quotient.mk _ (interpretName name environment))
              (.cons (scopedBodyEquiv algebra (stage target).unop [Srt.nm] Srt.pr
                ((meaning operations value).app (stage target) (contextPoint environment))) .nil))) .nil)) := by
  simp only [NamePassing.Presentation.carrier, meaning]
  dsimp only [Operations.carrier]
  simp only [NatTrans.comp_app_apply]
  rw [CategoricalOperations.abstraction_future, Functor.map_id_apply]
  change programsAtEquiv algebra .pr (stage target)
    ((CategoricalOperations.parallel algebra).app (stage target)
      (((((meaning operations body).app (stage target) (contextPoint environment)).app
        (stage target) (𝟙 _)) (rawPoint result)),
        (CategoricalOperations.input algebra).app (stage target)
          ((nameMeaning operations name).app (stage target) (contextPoint environment),
            (meaning operations value).app (stage target) (contextPoint environment)))) = _
  rw [CategoricalOperations.parallel_readout, CategoricalOperations.input_readout,
    nameMeaning_readout, rawPoint_readout]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
