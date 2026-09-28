import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedAuthoredContexts
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mettapedia.OSLF.Syntax.RhoSourceEquationModel

/-!
# Located rho events and the equation-context quotient

The source name equation identifies substitutions in the context category,
but a located operational event can still retain the raw name used by that
substitution. This gives a concrete obstruction to descending the existing
proof-relevant event presheaf to the equation-quotient context category.
Equation-class states do descend; the event comparison therefore needs a
separate quotient or a base retaining the relevant occurrence data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEventQuotientDescentBoundary

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEquationModel
open Mettapedia.OSLF.Binding.ContextualLocatedEvents
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents

abbrev nameContext : Ctx sig := [Srt.nm]

/-- Substitute the source's reflected name for the single free name. -/
def reflectedSub : Sub sig nameContext nameContext
  | _, .zero => quotedDroppedName
  | _, .succ impossible => nomatch impossible

/-- Keep the single free name unchanged. -/
def identitySub : Sub sig nameContext nameContext :=
  fun _ v => .var v

/-- A retained communication occurrence sees the difference before quotienting. -/
theorem located_distinguishes_substitutions :
    (RhoExample.located.map identitySub).target ≠
      (RhoExample.located.map reflectedSub).target := by
  decide

abbrev rawClone := termClone sig
noncomputable abbrev sourceClone :=
  (BindingEquationQuotientModel.algebra rhoSourceE).substitution.toClone
abbrev rawName : ContextObject rawClone :=
  ContextObject.ofList rawClone nameContext

def identityArrow : rawName ⟶ rawName :=
  rawClone.operationAsSingletonMorphism nameVariable

def reflectedArrow : rawName ⟶ rawName :=
  rawClone.operationAsSingletonMorphism quotedDroppedName

/-- The actual raw-to-source-equation context functor. -/
noncomputable def quotientBase :
    (ContextObject rawClone) ⥤ (ContextObject sourceClone) :=
  termCloneToSemanticContextFunctor sig ⋙ quotientContextFunctor rhoSourceE

/-- The authored reflection equation identifies the two substitutions. -/
theorem quotient_arrows_equal :
    quotientBase.map identityArrow = quotientBase.map reflectedArrow := by
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  change (Quotient.mk _ nameVariable : TermQ rhoSourceE nameContext Srt.nm) =
    (Quotient.mk _ quotedDroppedName : TermQ rhoSourceE nameContext Srt.nm)
  exact Quotient.sound (EqClosure.symm quote_drop_source_equation)

/-- The retained COMM/Drop events indexed by raw substitution contexts. -/
def rawEvents : ((ContextObject rawClone)ᵒᵖ) ⥤ Type :=
  (cloneContextToSyntactic sig).op ⋙
    presentationEventPresheaf rhoSourceWithDrop.toUnpositioned Srt.pr

/-- The quotient-equal substitutions act differently on retained events. -/
theorem raw_arrows_act_differently :
    rawEvents.map identityArrow.op ≠ rawEvents.map reflectedArrow.op := by
  intro equal
  let event : PresentationInstance rhoSourceWithDrop.toUnpositioned
      nameContext Srt.pr := ⟨⟨0, by decide⟩, RhoExample.located⟩
  have atEvent := congrArg
    (fun morphism : rawEvents.obj (Opposite.op rawName) ⟶
        rawEvents.obj (Opposite.op rawName) =>
      morphism event) equal
  have targetEqual := congrArg PresentationInstance.target atEvent
  change (RhoExample.located.map identitySub).target =
    (RhoExample.located.map reflectedSub).target at targetEqual
  exact located_distinguishes_substitutions
    targetEqual

/-- The actual retained COMM/Drop event presheaf cannot be the pullback of
an event presheaf on the source equation-quotient context category. The
obstruction is the authored quote/drop equation itself, not a failure of
ordinary substitution naturality. -/
theorem raw_events_do_not_descend :
    ¬ ∃ (events : ((ContextObject sourceClone)ᵒᵖ) ⥤ Type),
      Nonempty (rawEvents ≅ quotientBase.op ⋙ events) := by
  rintro ⟨events, ⟨comparison⟩⟩
  apply raw_arrows_act_differently
  have equalAfterQuotient :
      (quotientBase.op ⋙ events).map identityArrow.op =
      (quotientBase.op ⋙ events).map reflectedArrow.op := by
    simp [quotient_arrows_equal]
  have first := comparison.hom.naturality identityArrow.op
  have second := comparison.hom.naturality reflectedArrow.op
  rw [equalAfterQuotient] at first
  exact (cancel_mono (comparison.hom.app (Opposite.op rawName))).mp
    (first.trans second.symm)

end Mettapedia.OSLF.Binding.RhoEventQuotientDescentBoundary
