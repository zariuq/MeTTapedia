import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SynchronousStaticSourceTerm

/-!
# Actual finite static support transport

Lambda and synchronous rho discharge the declaration inventories required by
the common support theorem. The synchronous witness has an open name and a
boundary parameter with nonempty target support. Removing that support is
rejected rather than inferred from ordinary typing.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteStaticSupportControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted ContinuationDecorationProfile LambdaContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem lambda_static_support
    (color : CostStaticColor) {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors lambdaIGSLT.presentation.presentation.language
      (· ∈ (ofRetypingPlan lambdaContinuationRetyping).wrappedLabels) free bound pattern type)
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.toHasType.ReflectiveSupportSafeAt .empty support available
      (mapTypeExpr (color.symbolsOf lambdaIGSLT))) :
    ((ofRetypingPlan lambdaContinuationRetyping).mapStatic_hasType
      FiniteStaticTypingControls.lambda_nonprincipal color typed).ReflectiveSupportSafeAt
        ((ofRetypingPlan lambdaContinuationRetyping).costWholeReflectionProfile .empty)
        support available id :=
  (ofRetypingPlan lambdaContinuationRetyping).mapStatic_reflectiveSupport
    FiniteStaticTypingControls.lambda_nonprincipal lambdaBareCollectionConstructorsWrapped
    .empty color typed safe

/-- Every term of the constructed synchronous source fibre retains its
certified target support after static transport and ambient reinsertion. -/
theorem synchronous_reinsert_support
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr} {sort : LangSort Synchronous.rhoSyncCalc}
    (term : Synchronous.communicationDecoration.StaticSourceTerm
      Synchronous.FiniteWhole.sourceReflection color free support sourceBound targetBound sort)
    (thinning : CostStaticTypeThinning Synchronous.rhoSyncIGSLT color sourceBound targetBound) :
    (term.reinsert_hasType FiniteStaticTypingControls.synchronous_nonprincipal thinning).ReflectiveSupportSafeAt
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1) support targetBound id :=
  term.reinsert_reflectiveSupport FiniteStaticTypingControls.synchronous_nonprincipal
    CanonicalInventory.synchronous_bareConstructorsAllowed thinning

/-- This is the actual normalized open frame, including its nonempty
dependency suffix, rather than an empty-support specialization. -/
theorem synchronous_normalized_open_frame_support (color : CostStaticColor) :
    let term := Synchronous.StaticSource.normalize
      (Synchronous.StaticSource.Controls.openFrameTerm color)
    let thinning : CostStaticTypeThinning Synchronous.rhoSyncIGSLT color [.base "Name"]
      (Synchronous.StaticSource.Controls.targetBinders color) := .mapped (.base "Name") .nil
    (term.reinsert_hasType FiniteStaticTypingControls.synchronous_nonprincipal thinning).ReflectiveSupportSafeAt
      (Synchronous.communicationDecoration.costWholeReflectionProfile
        Synchronous.FiniteWhole.sourceReflection.1)
      (Synchronous.StaticSource.Controls.frameSupport color)
      (Synchronous.StaticSource.Controls.targetBinders color) id :=
  synchronous_reinsert_support _ _

theorem boundaryTyped : HasType Synchronous.rhoSyncCalc Synchronous.StaticSource.Controls.frameFree
    [.base "Name"] (.fvar "hole") (.base "Proc") :=
  .fvar (by simp [Synchronous.StaticSource.Controls.frameFree])

/-- Ordinary typing does not authorize discarding a boundary's nonempty
target support, as would happen at an unproved quotation crossing. -/
theorem boundary_cannot_lose_support (color : CostStaticColor) :
    ¬ boundaryTyped.ReflectiveSupportSafeAt ReflectionExtension.rhoReflectionProfile
      (Synchronous.StaticSource.Controls.frameSupport color) [] id := by
  intro safe
  cases safe with
  | fvar lookup available shape =>
      obtain ⟨inner, same⟩ := shape
      have lengths := congrArg List.length same
      simp [Synchronous.StaticSource.Controls.frameSupport,
        Synchronous.StaticSource.Controls.targetBinders] at lengths

end Mettapedia.GSLT.LanguageDef.FiniteStaticSupportControls
