import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPreparedViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance

/-! # Authored schema views at the native candidate-step boundary

The physical opening algorithm is applied to the existing native firing and
its conditional stored rows. Its scalar bundle recovers the actual prepared
rule, selected views and reservation ledger. Conditions are retained; this
connection does not restrict the rule to the positive, check-free profile.
Admission, solver results and publication recipes remain those of `native`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativePreparation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface
open SchemaPreparation

variable {S : Signature} {O : Type}
  {Γ : Ctx S} {sort : S.Srt} {s : NativeState S O Γ sort}
  (code : Intrinsic.HeadPresentation (TargetSignature s.locals s.state.declarations))

def prepare? (f : NativeFiring s) : Option (Views Payloads.Term) :=
  prepareViews? s.locals s.state.declarations code s.state.occupied f.selection f.rule
    (fun occurrence => (s.state.rows occurrence).value)

theorem prepare_exact (f : NativeFiring s) :
    prepare? code f =
      some ((viewsOf s.locals s.state.declarations f.prepared).map (Intrinsic.lower code)) :=
  prepareViews_exact s.locals s.state.declarations code s.state.occupied f.selection f.rule _

theorem prepare_unique (f : NativeFiring s) :
    ∃! physical, prepare? code f = some physical := by
  refine ⟨_, prepare_exact code f, ?_⟩
  intro physical computed
  rw [prepare_exact] at computed
  exact (Option.some.inj computed).symm

theorem source_readback [DecidableEq S.Srt] (f : NativeFiring s) {physical : Views Payloads.Term}
    (computed : prepare? code f = some physical) :
    readSourceViews? s.locals s.state.declarations code Γ sort (printViews physical) =
      some (viewsOf s.locals s.state.declarations f.prepared) :=
  prepared_source_views_readback s.locals s.state.declarations code s.state.occupied f.selection f.rule _ computed

theorem checks_retained (f : NativeFiring s) {physical : Views Payloads.Term}
    (computed : prepare? code f = some physical) :
    physical.rule.checks = f.prepared.rule.checks.map (Check.map (Intrinsic.lower code)) := by
  rw [prepare_exact] at computed
  rw [← Option.some.inj computed]
  rfl

theorem ports_and_ledger_retained (f : NativeFiring s) {physical : Views Payloads.Term}
    (computed : prepare? code f = some physical) :
    physical.taken.length = f.selection.taken.length ∧
    physical.read.length = f.selection.read.length ∧
    physical.occupied = ContextualActivationScopes.after s.state.occupied f.selection := by
  rw [prepare_exact] at computed
  rw [← Option.some.inj computed]
  simp only [Views.map, viewsOf, List.length_map, List.length_ofFn, true_and]
  rfl

/-- Opening depends on the selected rule and ports, not on the recipe that
will publish an admitted result. The latter cannot be discarded from a firing. -/
theorem preparation_congr {f g : NativeFiring s}
    (rule : f.rule = g.rule) (selection : f.selection = g.selection) :
    prepare? code f = prepare? code g := by
  simp only [prepare?, rule, selection]

variable [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

abbrev profile := (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep

/-- Every actual native event has computed source views of its own candidate.
Its permission and published endpoint come from the native event, not from
successful decoding or opening. -/
theorem event_source_views {t : NativeState S O Γ sort}
    (event : profile.effectCore.Event profile.eventAdmission s t) :
    ∃ physical, prepare? code event.firing = some physical ∧
      readSourceViews? s.locals s.state.declarations code Γ sort (printViews physical) =
        some (viewsOf s.locals s.state.declarations event.firing.prepared) ∧
      ∃ admitted : event.firing.Realized,
        publishedState event.firing.recipes (event.firing.pinned admitted).firing = t := by
  obtain ⟨physical, computed, _⟩ := prepare_unique code event.firing
  refine ⟨physical, computed, source_readback code event.firing computed, event.permitted, ?_⟩
  exact event.target_eq

#print axioms prepare_unique
#print axioms source_readback
#print axioms checks_retained
#print axioms event_source_views

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativePreparation
